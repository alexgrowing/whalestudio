import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.LKCount
  GlobalTheory.LKCount.OrbKProd GlobalTheory.BCT UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

variable {p : ℕ} [Fact p.Prime]

private def atHom {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) : G.GAf →* GL (Fin G.n) k :=
  (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k)).comp
    ((MonoidHom.fst _ _).comp (Subgroup.subtype _))

private theorem charpoly_at_toAfF {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) :
    (P.at (toAfF G β x t hx y)).charpoly = (P.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly := by
  have h := Matrix.charpoly_units_conj (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k) x)
    (P.ι ((y.1.1 : G.Cˣ) : G.C))
  rw [← h, ← P.κ_ι]
  have e : P.at (toAfF G β x t hx y) =
      P.κ (x : AfP p ⊗[ℚ] G.C) * P.κ (1 ⊗ₜ ((y.1.1 : G.Cˣ) : G.C)) * P.κ ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    rw [← map_mul, ← map_mul]
    rfl
  rw [e, ← Matrix.coe_units_inv]
  rfl

private theorem toAfF_cent_comm {G : HTGroup p} (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
    ∀ b ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y), a * b = b * a := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC ((y.1.1 : G.Cˣ) : G.C) hsep hdeg
  have hcent : ∀ w : G.C, w * ((y.1.1 : G.Cˣ) : G.C) = ((y.1.1 : G.Cˣ) : G.C) * w ↔
      w ∈ Set.range ((Algebra.adjoin G.F ({((y.1.1 : G.Cˣ) : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
    intro w
    constructor
    · intro h
      have hw : w ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by
        rw [Subalgebra.mem_centralizer_iff]
        simpa using h.symm
      rw [hcsa] at hw
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      have hw : (v : G.C) ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by rw [hcsa]; exact v.2
      rw [Subalgebra.mem_centralizer_iff] at hw
      exact (hw _ rfl).symm
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y.1.1 with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C) := rfl
  have hδ : ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have conj : ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
      (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
          ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) *
          (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
    intro a ha
    have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
    simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
    rw [hδ] at h1
    set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
      calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
        _ = U * (x⁻¹ * A * x) := by group
    rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]
  intro a ha b hb
  have hc := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ ((y.1.1 : G.Cˣ) : G.C) _ hcent _ _ (conj a ha) (conj b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

private theorem twisted_centralizer_commutative {G : HTGroup p} (β : G.Cˣ) (y : grp G β)
    (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y),
    ∀ b ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), a * b = b * a := by
  have hrho : ∀ w, (G.rho w ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable := by
    intro w
    letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
    have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
      fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
    let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
    have h := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F (G.Fw w) G.C G.n G.rankC g _ hdeg
    have e : g ((y.1.1 : G.Cˣ) : G.C) = G.rho w ((y.1.1 : G.Cˣ) : G.C) := rfl
    rw [e] at h
    rw [h]
    exact hsep.map
  have hb := GlobalTheory.TorCls.AtP.inclG_one_bijective G
  have hy : toP1 G β y = inclG G 1 (locC G y.1) := rfl
  have key : ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), ∃ a' : Gp G, inclG G 1 a' = a ∧
      a' * locC G y.1 = locC G y.1 * a' := by
    intro a ha
    obtain ⟨a', rfl⟩ := hb.2 a
    refine ⟨a', rfl, hb.1 ?_⟩
    rw [map_mul, map_mul, ← hy]
    exact ha
  intro a ha b hb'
  obtain ⟨a', rfl, ha'⟩ := key a ha
  obtain ⟨b', rfl, hb''⟩ := key b hb'
  rw [← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (mul_comm _ _) (funext fun w => ?_)
  exact GlobalTheory.CentSep.centraliser_comm_of_separable (G.Fw w) (Fin G.n) ((locC G y.1).2 w) (a'.2 w) (b'.2 w) (hrho w)
    (congrFun (congrArg Prod.snd ha') w) (congrFun (congrArg Prod.snd hb'') w)

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.vanForms :
    UpperTheory.Gal.Spc.VanForms := by
  intro p _ G _ Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ f hf hC hR B x t hx y hy
  by_cases hs1 : (P₁.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable
  · have hns := GlobalTheory.SepCharpoly.not_separable_charpoly G.F k₁ G.C G.n P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hle := GlobalTheory.VanishNonEll.natDegree_minpoly_le G.F k₁ G.C G.n G.n_pos P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n := by
      by_contra h
      exact hns (Or.inl (lt_of_le_of_ne hle h)) hs1
    have hms : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable := by
      by_contra h
      exact hns (Or.inr ⟨hdeg, h⟩) hs1
    have hirr : ¬ Irreducible (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)) := fun h => hy ⟨hdeg, hms, h⟩
    have hcp := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F k G.C G.n G.rankC P.ι ((y.1.1 : G.Cˣ) : G.C) hdeg
    have hat := charpoly_at_toAfF P B.β x t hx y
    rw [hcp] at hat
    have hδs : (P.at (toAfF G B.β x t hx y)).charpoly.Separable := by
      rw [hat]
      exact hms.map
    have hδi : ¬ Irreducible (P.at (toAfF G B.β x t hx y)).charpoly := by
      rw [hat]
      exact GlobalTheory.VanishNonEll.not_irreducible_map _ _ (minpoly.monic (IsIntegral.of_finite G.F _)) hirr
    have hT₁ := toAfF_cent_comm B.β x t hx y hdeg hms
    have hT₂ := twisted_centralizer_commutative B.β y hdeg hms
    have h1 := orbK_eq_zero_of_cuspSlices S f hf hC _ hδs hδi hT₁
    have hbi : Formalism.UG.IsBiInv Lv.K.toSubgroup f := hf.1
    refine orbK_prod_eq_zero_of_slices Lv.K.toSubgroup (Kp G) (toAfF G B.β x t hx y) (toP1 G B.β y) _ hT₁ hT₂ ?_ fun z => ?_
    · intro c hc w
      rw [Subgroup.mem_prod] at hc
      have e1 : f (c.1⁻¹ * w.1 * c.1) = f w.1 :=
        hbi ⟨c.1⁻¹, Subgroup.inv_mem _ hc.1⟩ ⟨c.1, hc.1⟩ _
      have e2 : oneP G (c.2⁻¹ * w.2 * c.2) = oneP G w.2 := by
        have hiff : c.2⁻¹ * w.2 * c.2 ∈ Kp G ↔ w.2 ∈ Kp G := by
          rw [(Kp G).mul_mem_cancel_right hc.2, (Kp G).mul_mem_cancel_left ((Kp G).inv_mem hc.2)]
        unfold oneP
        by_cases hw : w.2 ∈ Kp G
        · rw [Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hiff.2 hw),
            Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hw)]
          rfl
        · rw [Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from fun h => hw (hiff.1 h)),
            Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from hw)]
      show f (c.1⁻¹ * w.1 * c.1) * oneP G (c.2⁻¹ * w.2 * c.2) = f w.1 * oneP G w.2
      rw [e1, e2]
    · unfold orbK at h1 ⊢
      rw [orbC_eq] at h1 ⊢
      have e : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) : Set G.GAf)
          (Lv.K.toSubgroup : Set G.GAf),
          oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y)
            (fun v => f v * oneP G z) (Quotient.out q) =
          oneP G z * oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y) f
            (Quotient.out q) := by
        intro q
        unfold oTerm
        ring
      rw [finsum_congr e]
      exact finsum_mul_eq_zero _ _ h1
  · refine GlobalTheory.orbK_eq_zero_of_charpoly_not_separable _ k₁ G.n ((atHom P₁).comp (MonoidHom.fst _ _)) _ _ _ ?_ ?_
    · intro g hg
      exact hR g.1 (left_ne_zero_of_mul hg)
    · intro h
      apply hs1
      rw [← charpoly_at_toAfF P₁ B.β x t hx y]
      exact h
