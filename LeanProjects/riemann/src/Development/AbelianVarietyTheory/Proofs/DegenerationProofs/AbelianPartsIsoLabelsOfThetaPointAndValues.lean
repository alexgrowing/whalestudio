import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesCubeValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesSymmetryValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianPartIsoThetaSectionScaleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionThetaStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductIsoOfFibreIsoFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionMapOfThetaMatchingStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
section
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F} (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A}

theorem Carries.eq {ν : NumOf D F N} {ν' : NumOf D' F N'} {x : N.A} {x' : N'.A} (h : Carries ν ν' φ x x') :
    lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _ = ν'.eA x' := by
  rw [← Category.assoc, h, lift_snd]

theorem exists_equiv (hφ : HomF φ) : ∃ f : N.A ≃* N'.A, ∀ x, Carries ν ν' φ x (f x) := by
  have hi : φ.inv ≫ fst _ _ = fst _ _ := by rw [Iso.inv_comp_eq, hφ.1]
  have c : ∀ x, Carries ν ν' φ x (ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) := fun x => by
    unfold Carries
    ext1
    · rw [Category.assoc, hφ.1, lift_fst, lift_fst]
    · rw [lift_snd, MulEquiv.apply_symm_apply, Category.assoc]
  let f : N.A →* N'.A := MonoidHom.mk' (fun x => ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) fun x y => by
    rw [map_mul ν.eA, hφ.2, map_mul]
  refine ⟨MulEquiv.ofBijective f ⟨fun x y h => ?_, fun y => ?_⟩, c⟩
  · have e : lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν.eA y) ≫ φ.hom :=
      (c x).trans ((congrArg (fun z => lift (𝟙 _) (ν'.eA z)) h).trans (c y).symm)
    have := congrArg (· ≫ snd _ _) ((cancel_mono _).1 e)
    simp only [lift_snd] at this
    exact ν.eA.injective this
  · refine ⟨ν.eA.symm (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _), ν'.eA.symm_apply_eq.2 ?_⟩
    have e : lift (𝟙 _) (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _) = lift (𝟙 _) (ν'.eA y) ≫ φ.inv := by
      ext1
      · rw [Category.assoc, hi, lift_fst, lift_fst]
      · rw [lift_snd, Category.assoc]
    rw [MulEquiv.apply_symm_apply, e, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

theorem wVal_ne (w : BunIso φ) {f : N.A → N'.A} {x : N.A} (h : Carries ν ν' φ x (f x)) : wVal ν ν' w f x ≠ 0 := by
  have z : Sp F := (default : PrimeSpectrum F)
  have e₁ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left =
      (ν'.eA (f x)).left := by
    rw [← Over.comp_left, h.eq]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [e₁]; exact ν.good _ trivial
  have m₂ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) z ∈
      D'.P.L.U (ν'.J (ν'.eA (f x)).left) := by rw [e₂]; exact ν'.good _ trivial
  intro h0
  have := toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ z
    (show _ ∈ (LB.div (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)
      (D.P.L.pull (snd (TF (R := R) F) D.P.A).left)).U
        (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left) from ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩)
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left))
  exact Units.ne_zero _ (this.symm.trans ((congrArg (toStk z) h0).trans (map_zero _)))

theorem exists_iso (hG : GlobalFnsSt) (w : BunIso φ) (hφ : HomF φ) (hw : w.IsGen) (hne : ∃ x, N'.th x ≠ 0) :
    ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧ ∀ x, Carries ν ν' φ x (I.φ x) := by
  obtain ⟨f, hf⟩ := exists_equiv ν ν' hφ
  have h₁ := GlobalTheory.T.abelianPartIso_carries_cube_values hG R D D' F N N' ν ν' φ w f hφ hw hf
  have h₂ := GlobalTheory.T.abelianPartIso_carries_symmetry_values hG R D D' F N N' ν ν' φ w f hφ hw hf
  obtain ⟨c, h₃⟩ := GlobalTheory.T.exists_abelianPartIso_theta_section_scale R D D' F N N' ν ν' φ w f hφ hw hf
  have h₀ := fun x => wVal_ne ν ν' w (hf x)
  have hc : c ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := f.surjective x
    rintro rfl
    exact hx (by rw [h₃, zero_mul, zero_mul])
  have h1 := h₀ 1
  refine ⟨⟨f, fun x => Units.mk0 (wVal ν ν' w f x / wVal ν ν' w f 1) (div_ne_zero (h₀ x) h1), Units.ext (div_self h1),
    fun x y u => Units.ext ?_, fun x => Units.ext ?_, Units.mk0 (c * wVal ν ν' w f 1) (mul_ne_zero hc h1), fun x => ?_⟩,
    ⟨φ, w, wVal ν ν' w f, hφ.1, hw, hf, fun _ => rfl, fun x => div_mul_cancel₀ _ h1⟩, hf⟩
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₁ x y u
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₂ x
  · simp only [Units.val_mul, Units.val_mk0]
    rw [h₃]
    field_simp
end

theorem main : Laws → ThetaPtDeterminesSt → BrUthSt → UrCSt := by
  intro hL hQ hU R _ _ D D' e₁ b₁ e₂ b₂ C _ _ _ _ _ N N' ν ν' q q' n hn ho hnC hI hI' hT hT' mt hA hg e hB hTm
  have hn0 : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at hnC; exact zero_ne_one hnC
  obtain ⟨Q, Φ, hΦ⟩ := exists_isFib hL.polBaseChange D C
  obtain ⟨Q', Φ', hΦ'⟩ := exists_isFib hL.polBaseChange D' C
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta hL hQ hU R D D' e₁ b₁ e₂ b₂ hg C N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hn0
  choose ρ hρ hρ' hρ'' using GlobalTheory.T.exists_torsion_map_of_theta_matching C N N' q q' n _ _ hn ho hnC hI hI' hT hT' mt hA e hTm
  have key : ∀ j, j₀ ≤ j → ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧
      ∀ b, b ^ (n ^ j) ^ 2 = 1 → I.φ b = ρ j b := fun j hj => by
    obtain ⟨σ, hσ, hs⟩ := H j hj _ _ mt.c₀_ne (hρ j)
    obtain ⟨φ, w, hφ, hw, hp⟩ := GlobalTheory.T.exists_product_iso_of_fibre_iso_field R D D' C Q Q' Φ Φ' hΦ hΦ' σ hσ
    obtain ⟨t, -, ht⟩ := hT'.good 1
    obtain ⟨I, hI, hc⟩ := exists_iso ν ν' hL.globalFns w hφ hw ⟨_, fun h => by
      rw [h, norm_zero] at ht; exact zero_ne_one ht⟩
    refine ⟨I, hI, fun b hb => ν'.eA.injective ?_⟩
    exact (hc b).eq.symm.trans (Carries.eq (hp _ _ fun x hx => hs x b hb hx))
  obtain ⟨I, hG, hI₀⟩ := key (j₀ + 1) (Nat.le_succ _)
  have om : ∀ j, Odd (n ^ j) := fun j => ho.pow
  refine ⟨I, fun i p p' hr h1 h1' => ?_, ?_, hG⟩
  · obtain ⟨I', -, hI₁⟩ := key (j₀ + 1 + i) (by omega)
    have ag : ∀ b, b ^ (n ^ (j₀ + 1)) ^ 2 = 1 → I'.φ b = I.φ b := fun b hb => by
      obtain ⟨p, p', hr, a, a', rfl⟩ := hρ'' _ b hb
      rw [hI₀ _ hb, ← hρ' _ _ le_rfl p p' hr a a', hI₁, ← hρ' _ _ (by omega) p p' hr a a']
      rw [pow_add, mul_pow, pow_mul, hb, one_pow]
    have eq : ∀ x, I'.φ x = I.φ x := fun x => by
      refine hT'.sep (j₀ + 1) (by omega) _ _
        ((I'.lam * I'.h x ^ (n ^ (j₀ + 1)) ^ 2 / (I.lam * I.h x ^ (n ^ (j₀ + 1)) ^ 2) : Cˣ) : C) (Units.ne_zero _)
        fun b' hb' => ?_
      obtain ⟨b, rfl⟩ := I.φ.surjective b'
      have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := I.φ.injective (by rw [map_pow, hb', map_one])
      rw [RecPeriods.uth_iso I _ (om _) b x hb, ← ag b hb, RecPeriods.uth_iso I' _ (om _) b x hb, ← _root_.mul_assoc,
        ← Units.val_mul, div_mul_cancel]
    have hb : p.1.2.b ^ n ^ i = 1 := by rw [N.QT_pow_b, h1, toAdd_one, N.c_zero]
    rw [← eq, hI₁, hρ' (j₀ + 1 + i) i (by omega) p p' hr h1 h1']
    rw [← pow_mul, show (j₀ + 1 + i) * 2 = i + (2 * j₀ + 2 + i) by ring, pow_add, pow_mul, hb, one_pow]
  · obtain ⟨t, ht, ht'⟩ := hT.good 1
    have dv : ∀ (j : ℕ) (x : N.A), ∃ y, y ^ n ^ j = x := fun j => by
      induction j with
      | zero => exact fun x => ⟨x, by rw [pow_zero, pow_one]⟩
      | succ j ih =>
        intro x
        obtain ⟨y, rfl⟩ := hT.div x
        obtain ⟨z, rfl⟩ := ih y
        exact ⟨z, by rw [pow_succ, pow_mul]⟩
    obtain ⟨b, rfl⟩ := dv (j₀ + 1) t
    have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := by
      rw [sq, pow_mul, pow_succ' n j₀, pow_mul _ n, ← pow_succ', ht, one_pow]
    have a := RecPeriods.uth_iso I _ (om _) b 1 hb
    rw [map_one, hI₀ b hb, ((hρ _).2 b hb).2, I.h_one, one_pow, _root_.mul_one] at a
    have nz : N.uth (n ^ (j₀ + 1)) b 1 ≠ 0 := by
      refine mul_ne_zero (Units.ne_zero _) (mul_ne_zero (fun h => ?_) (Units.ne_zero _))
      rw [_root_.one_mul] at ht' h
      rw [h, norm_zero] at ht'
      exact zero_ne_one ht'
    exact (mul_right_cancel₀ nz a).symm

end GlobalTheory.Ex.AbPartIso
end
