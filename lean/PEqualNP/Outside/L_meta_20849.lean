import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20849 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25364513 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 16]⟩], 19⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
