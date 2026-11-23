import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.LabTrans GlobalTheory.SeriesCompare GlobalTheory.ArcPull

theorem recognition_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  intro R _ _ _ hR D A lab n hn ho hu hT hgal htheta W _ _ _ hW φ iφ lφ G' _ _ D' A' U' a hG' hfib
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩

  obtain ⟨W₀, _, _, _, φ₀, G₀, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG₀, fib₀, c₀, H₀⟩ := hT
  have := hW₀.1
  have := hW₀.2.2
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  obtain ⟨g₀, hg₀, hg₀'⟩ := exists_goodLab b₀ hG₀ U₀ (Kb W₀)
  have Glab : GoodLab D.toPre A (Kb R) lab := by
    refine (goodLab_move h₀ c₀ em₀ D₀.tau_bimult fib₀ lab g₀ fun k hk p => ?_).2 hg₀
    obtain ⟨ga₀, hga₀, gp₀, -⟩ := fib₀
    obtain ⟨x, hx⟩ := exists_lift_pt gp₀.1 em₀.toRingHom
      (em₀.comp_algebraMap.trans (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
        (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (hga₀ r).symm)))) (lab k p)
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff h₀ c₀ em₀ D₀.tau_bimult p _).2 rfl
    rw [← (hg₀' k hk _ x).1 (H₀ k hk p p₁ _ x t₁ t₂ t₃ hx)]
    exact hx

  haveI := lφ
  obtain ⟨DW, ⟨hWp⟩⟩ := GlobalTheory.MumPull.exists_pull R W φ iφ lφ D
  have hBW := DW.tau_bimult
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := GlobalTheory.T.exists_complete_isAlgClosed_cExt' W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp (fracMap iφ)).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (fracMap_algebraMap iφ r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) C

  obtain ⟨ε, hε, -, -, -⟩ := exists_ptHom hfib cC em
  let fW : ∀ k, QkPt DW.toPre C k → (TFK (R := W) C ⟶ A'.A) := fun k q =>
    if hk : 1 ≤ k then ε (lab k ((Equiv.ofBijective _ (tr_bij hWp cC em hBW hk)).symm q)) else 1
  have hfW : ∀ k (hk : 1 ≤ k) p, fW k (tr hWp cC em hBW p) = ε (lab k p) := fun k hk p => by
    simp only [fW, dif_pos hk, Equiv.ofBijective_symm_apply_apply]
  have GW : GoodLab DW.toPre A' C fW := (goodLab_move hWp cC em hBW hfib lab fW fun k hk p => by
    rw [hfW k hk p]; exact (hε _ _).1 rfl).1 Glab
  obtain ⟨f', G'', hf'⟩ := exists_goodLab bW hG' U' C

  have hO : CExt W ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := maximalIdeal W) hr)⟩
  have huW : IsUnit (n : W) := by simpa using hu.map φ
  have h1 : ‖(n : C)‖ = 1 := (isUnit_iff_norm hC n).1 huW
  have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨N₁, ν₁, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W DW.toPre DW.psi_even hBW C ⊤ fun _ => trivial
  obtain ⟨N, ν, q₀, -, hIν, hq₀, -⟩ := exists_integral hW DW hC ν₁
  have hT := GlobalTheory.ValuesTorsion.tors_of_integral hL hL₂ (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) W DW.toPre DW.psi_even hBW C hO N ν hIν n hn
    ho h1
  have hd : ∀ g : N.Gt, ∃ g', g' ^ n = g := fun g => by
    obtain ⟨g', hg'⟩ := (GlobalTheory.Ex.QStr.qStructure C N n _ hnC hT 1).2.1 g
    exact ⟨g', by rw [← hg', pow_one]⟩
  have h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0 := by
    obtain ⟨h, -, -, hh⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q₀ hq₀ n _ hn ho h1 hT 1 le_rfl).2.2 1
    exact ⟨_, hh⟩
  obtain ⟨N', ν', -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial

  have galW : ∀ k, (∃ j, k = n ^ j) → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C k),
      QkExt (σ : C →+* C) p pσ → (fW k pσ).left = spMap (σ : C →+* C) ≫ (fW k p).left := by
    rintro k ⟨j, rfl⟩ σ p pσ hp
    have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
    obtain ⟨p₀, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    let σR : C →ₐ[FractionRing R] C := ⟨(σ : C →+* C), fun t => σ.commutes (fracMap iφ t)⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Kb R →ₐ[FractionRing R] Kb R, em.toRingHom.comp ρ.toRingHom = (σR.comp em).toRingHom := by
      letI : Algebra (Kb R) C := em.toRingHom.toAlgebra
      haveI : IsScalarTower (FractionRing R) (Kb R) C := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
      exact ⟨(σR.comp em).restrictNormal (Kb R), RingHom.ext fun x => (σR.comp em).restrictNormal_commutes (Kb R) x⟩
    obtain ⟨p₀ρ, hρp⟩ := exists_ext hB ρ p₀
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p₀ _).2 rfl
    obtain ⟨r, hr⟩ := exists_ext hB σR p₁
    have u₁ := qkExt_trans t₁ hr
    obtain ⟨r', hr'⟩ := exists_ext hB em p₀ρ
    have u₂ := qkExt_trans hρp hr'
    rw [hρ] at u₂
    obtain rfl := ext_unique hB (σR.comp em) u₁ u₂
    have e₁ : pσ = tr hWp cC em hBW p₀ρ := (lies_iff hWp cC em hBW p₀ρ pσ).1 ⟨r, hr', by
      rw [hp.1, t₂, hr.1], isPullGtF_ext hWp cC (σ : C →+* C) σ.toAlgHom.comp_algebraMap t₃ hr hp⟩
    rw [e₁, hfW _ hk, hfW _ hk]
    obtain ⟨ga, -, gpa, -⟩ := hfib
    apply gpa.1.hom_ext
    · rw [(hε _ _).1 rfl, Category.assoc, (hε _ _).1 rfl, hgal ρ j p₀ p₀ρ hρp, ← Category.assoc,
        ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hρ]
      rfl
    · rw [Category.assoc, Over.w (ε (lab _ p₀ρ)), Over.w (ε (lab _ p₀))]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap σ.toAlgHom.comp_algebraMap)).symm
  have gal' : ∀ k, 1 ≤ k → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt D'.toPre C k),
      QkExt (σ : C →+* C) p pσ → (f' k pσ).left = spMap (σ : C →+* C) ≫ (f' k p).left := by
    intro k hk σ p pσ hp
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG' U' C C σ.toAlgHom k hk p
    obtain ⟨x', hx'⟩ := hx (f' k p)
    rw [← (hf' k hk pσ x').1 ((hiff pσ (f' k p) x' hp hx').1 ((hf' k hk p _).2 rfl))]
    exact hx'
  have gal : ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C ((n ^ 1) ^ 2))
      (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)), QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' →
      fW _ p = f' _ p' → fW _ pσ = f' _ pσ' := fun σ p pσ p' pσ' h₁ h₂ h₃ =>
    Over.OverMorphism.ext (by
      rw [galW _ ⟨2, by ring⟩ σ p pσ h₁, h₃, gal' _ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)) σ p' pσ' h₂])

  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D'.toPre D'.psi_even D'.tau_bimult C N' ν'
  have hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → fW ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q := by
    intro j
    have hm : Odd (n ^ j) := ho.pow
    have hk : 1 ≤ (n ^ j) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    have hum : IsUnit ((n ^ j : ℕ) : R) := by rw [Nat.cast_pow]; exact hu.pow j
    obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R hR D (n ^ j) hm hum _ id
    have Θ := htheta j v hv
    have hCR : CExt R (maximalIdeal R) C :=
      ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
    obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
    obtain ⟨J, hJX, hJ⟩ := GlobalTheory.Mum.OneTraitTheta.exists_values_iso hL hWp cC ν₀ ν
    choose q₀ hq₀ using fun i : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) =>
      exists_val D.psi_even hB ν₀ (qkExt hB em.toRingHom em.comp_algebraMap i)
    obtain ⟨s, hs⟩ := hv C hCR em N₀ ν₀ (fun i => qkExt hB em.toRingHom em.comp_algebraMap i) q₀
      (fun i => (qkExt_iff hB _ em.comp_algebraMap _ _).2 rfl) hq₀
    choose pp hpp using fun i => G''.onto _ hk (fW _ (tr hWp cC em hBW i)) (GW.pow _ hk _)
    choose qq hqq using fun i => exists_val D'.psi_even D'.tau_bimult ν' (pp i)
    have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G' hG' U' C hC N' ν' (n ^ j) hm _ pp qq
      (fun i => fW _ (tr hWp cC em hBW i)) (fun i => (hf' _ hk _ _).2 (hpp i).symm) hqq
    obtain ⟨c₃, hc₃⟩ := theta_prop hfib cC em hm (x := lab _) (x' := fun i => fW _ (tr hWp cC em hBW i))
      (fun i => by rw [hfW _ hk]; exact (hε _ _).1 rfl) (fun i => GW.pow _ hk _) Θ Q
    refine ⟨c₃ * s * J.lam, fun p p' q q' hp hp' hpp' => ?_⟩
    obtain ⟨i, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW i _).2 rfl
    obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
    have e₁ : N'.tx (n ^ j) (qq i) = N'.tx (n ^ j) q' :=
      GlobalTheory.ModelData.Scalar.tx_congr N' hm (((BG'.2.2.2.2 _).2.2 _ _ _ _ (hqq i) hp').1
        ((G''.eqv _ hk _ _).1 ((hpp i).trans hpp')))
    have e₂ := (GlobalTheory.RelabelCoords.series_iso J hm (p := q) (p' := q₀ i) (ν₀.eX.injective (by
      rw [hJX, hp.1, t₂, AddEquiv.apply_symm_apply]; exact (hq₀ i).1)) (hJ _ _ _ _ (hq₀ i).2 hp.2 t₃)).1
    rw [← e₁, hc₃ i, hs i, e₂, Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc,
      Units.mul_inv_cancel_left]

  obtain ⟨e, he⟩ := rec_trait hW hC ν ν' GW G'' hn ho huW hd gal hc h0
  obtain ⟨hD, T⟩ := GlobalTheory.LabTrans.exists_comp iφ Function.injective_id hWp e
  refine ⟨hD, C, inferInstance, inferInstance, inferInstance, inferInstance, em, cC, fun j p p₁ p'' x' h₁ h₂ h₃ h₄ => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  refine (hf' _ hk p'' x').2 ?_
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 h₁
  rw [(hε _ _).2 h₄, ← hfW _ hk p]
  obtain ⟨p₁', t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p _).2 rfl
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
  have cI : Compat (RingHom.id W) C := fun _ => rfl
  have g₁ := T.isPullGtF cC t₃ (isPullGtF_pullGt e hGF cI (tr hWp cC em hBW p).g)
  have g₂ := pullGt_unique hD cC g₁ h₃
  refine he j _ _ ?_ ?_
  · apply hD.xe.injective
    rw [h₂, AddEquiv.apply_symm_apply, ← T.xe_eq, AddEquiv.apply_symm_apply, t₂, AddEquiv.apply_symm_apply]
  · rw [← g₂]
    exact isPullGtF_pullGt e hGF cI _

end GlobalTheory.Mum.Recog
