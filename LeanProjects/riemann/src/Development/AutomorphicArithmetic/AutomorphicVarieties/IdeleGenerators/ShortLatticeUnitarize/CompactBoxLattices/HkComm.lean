import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private theorem ext_loc {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

private theorem comm_of_triv {w : Pl F} (g : GL (Fin 2) (w.adicCompletion F)) {k : GL (Fin 2) (Af F)}
    (hk : Matrix.GeneralLinearGroup.map (pLoc F w) k = 1) : k * locGL F 2 w g = locGL F 2 w g * k := by
  refine ext_loc fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = w
  · subst hx; rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem fix_loc (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
  fun k hk => hx _ ((hK F).2.2.2.2.2 c w k hk)

private theorem uop_mem (hR : HkReps) (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) := by
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨h1, h2⟩ := ha V _ x (fix_loc hK ρ c hx w)
  intro k hk
  have hkw : Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := (Subgroup.mem_iInf.1 hk) w
  set kw := Matrix.GeneralLinearGroup.map (pLoc F w) k with hkwe
  have hm : k * (locGL F 2 w kw)⁻¹ ∈ Kc c := mul_mem hk (inv_mem ((hK F).2.2.2.2.2 c w kw hkw))
  have ht : Matrix.GeneralLinearGroup.map (pLoc F w) (k * (locGL F 2 w kw)⁻¹) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, ← hkwe, mul_inv_cancel]
  have e : k = k * (locGL F 2 w kw)⁻¹ * locGL F 2 w kw := by rw [inv_mul_cancel_right]
  have h3 : ρ (locGL F 2 w kw) (Uop w (ρ.comp (locGL F 2 w)) (c w) x) = Uop w (ρ.comp (locGL F 2 w)) (c w) x := h1 kw hkw
  have h4 : ρ (k * (locGL F 2 w kw)⁻¹) x = x := hx _ hm
  rw [e, map_mul, Module.End.mul_apply, h3, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ρ _ (ρ (locGL F 2 w (a i)) x) = ρ (locGL F 2 w (a i)) x
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv _ ht, map_mul, Module.End.mul_apply, h4]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.hkComm :
    UpperTheory.V.Sd.Wc.HkReps → UpperTheory.V.Sd.Wc.KcTop → UpperTheory.V.Sd.Wc.HkComm := by
  intro hR hK F _ _ V _ _ ρ c x hx w
  refine ⟨uop_mem hR hK ρ c hx w, fun w' => ?_⟩
  by_cases hw : w' = w
  · subst hw; rfl
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨N', a', -, ha'⟩ := hR F w' (c w')
  rw [(ha V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w') w)).2, (ha' V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w) w')).2,
    (ha V _ _ (fix_loc hK ρ c hx w)).2, (ha' V _ _ (fix_loc hK ρ c hx w')).2]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change ρ (locGL F 2 w (a i)) (ρ (locGL F 2 w' (a' j)) x) = ρ (locGL F 2 w' (a' j)) (ρ (locGL F 2 w (a i)) x)
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv (a' j) (pLoc_locGL_of_ne hw (a i)), map_mul, Module.End.mul_apply]
