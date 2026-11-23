import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.RrCompCastSucc

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

theorem qminor_int {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n t : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  have hT : ∀ (s : ℂ) (i j : Fin n) (y : V), f (Tm E s i j y) = Tm E' s i j (f y) := by
    intro s i j y
    unfold Tm
    split_ifs <;> simp [hf, Module.algebraMap_end_apply]
  have hP : ∀ (m : ℕ) (g : Fin m → Module.End ℂ V) (g' : Fin m → Module.End ℂ V'),
      (∀ k y, f (g k y) = g' k (f y)) → ∀ y, f ((List.ofFn g).prod y) = (List.ofFn g').prod (f y) := by
    intro m
    induction m with
    | zero => intro g g' _ y; simp
    | succ m ih =>
      intro g g' h y
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      rw [h, ih (fun k => g k.succ) (fun k => g' k.succ) (fun k y => h k.succ y)]
  unfold qminor
  simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul,
    hP _ _ _ (fun k y => hT _ _ _ y)]

theorem thMap : ThMap := by
  intro V V' _ _ _ _ N E E' f hf u X x
  refine ⟨?_, qminor_int f hf _ _ _ _⟩
  simp only [Th, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, qminor_int f hf]

theorem keyId : KeyId := by
  intro V V' _ _ _ _ N E E' ι z f hE hι hz hf w cG hdet h0 v
  have h := congrArg f (algId V N E ι z hE hι hz (w + 1) v)
  rw [hdet] at h
  have hw : w + 1 - 1 = w := by ring
  rw [hw] at h
  have hT := thMap V V' N (fun a b => E (ι a) (ι b)) E' f hf w
  have hq : ∀ y, f (qdet (fun a b => E (ι a) (ι b)) w y) = 0 := by
    intro y
    rw [(hT (fun _ => y) 0).2]
    exact h0 _
  rw [← LinearMap.map_smul, h, map_sub, map_sum, hq, zero_sub]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hT _ c).1

end PositivityTheory.RgHe.SM
