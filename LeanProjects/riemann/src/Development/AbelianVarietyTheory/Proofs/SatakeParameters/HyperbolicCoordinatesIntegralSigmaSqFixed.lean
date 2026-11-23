import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem norm_iterate_le_one {p : ℕ} [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : ∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) (x : MaximalUnramifiedExtension p) (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖σ^[k] x‖ ≤ 1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih

theorem val_add_two_eq (D : D7) (p : ℕ) (t : ZMod (nP D p)) : (t + 2).val = (t.val + 2) % nP D p := by
  have : t + 2 = ((t.val + 2 : ℕ) : ZMod (nP D p)) := by push_cast; simp [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast]

theorem val_add_two_mod_two (D : D7) (p : ℕ) (hO : OrbitPlaces.OrbOK D p) (t : ZMod (nP D p)) :
    (t + 2).val % 2 = t.val % 2 := by
  have h2 : (2 : ℕ) ∣ nP D p := even_iff_two_dvd.mp hO.even
  rw [val_add_two_eq, Nat.mod_mod_of_dvd _ h2]
  omega

theorem sigma_sq_term (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p)
    (hc : σ^[nP D p] c = c) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hg : ∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N')
    (i : Fin r) (t : ZMod (nP D p)) :
    σ (σ (σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i)) =
      σ^[(t + 2).val] c * g (OrbitPlaces.orbMap D p z (t + 2)) a b i := by
  rw [map_mul, map_mul, hg]
  simp only [OrbitPlaces.orbMap]
  rw [val_add_two_eq, posPl_mod, posPl_add]
  congr 1
  rw [(show Function.IsPeriodicPt σ (nP D p) c from hc).iterate_mod_apply,
    Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem sigma_sq_sum_shift (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : ZMod (nP D p) → MaximalUnramifiedExtension p) (hF : ∀ t, σ (σ (F t)) = F (t + 2)) :
    σ (σ (∑ t, F t)) = ∑ t, F t := by
  rw [map_sum, map_sum]
  simp_rw [hF]
  exact Fintype.sum_equiv (Equiv.addRight 2) _ _ (fun _ => rfl)

theorem fOf_integral_sigma_sq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  intro D p _ σ om oms R N N' r g hO hσ hw hgn hg
  have hterm : ∀ (c : MaximalUnramifiedExtension p), ‖c‖ ≤ 1 → ∀ (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N') (i : Fin r) (t : ZMod (nP D p)),
      ‖σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i‖ ≤ 1 := by
    intro c hc z a b i t
    rw [norm_mul]
    exact mul_le_one₀ (norm_iterate_le_one σ hσ c hc _) (norm_nonneg _) (hgn _ _ _ _)
  refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩⟩
  · unfold fOf
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · exact hterm _ (hw.1 _).1 _ _ _ _ _
    · simp
  · unfold fOf
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · exact sigma_sq_term D p σ _ (hw.2 _).1 g hg _ _ _ _ t
    · simp
  · unfold fOf'
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · simp
    · exact hterm _ (hw.1 _).2 _ _ _ _ _
  · unfold fOf'
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · simp
    · exact sigma_sq_term D p σ _ (hw.2 _).2 g hg _ _ _ _ t

end GlobalTheory.KerStd.HypCoord
