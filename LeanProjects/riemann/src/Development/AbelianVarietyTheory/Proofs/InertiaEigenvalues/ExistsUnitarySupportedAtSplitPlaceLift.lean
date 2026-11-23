import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

theorem lift_map_eq_of_smul {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A) (hp : φ p = 1)
    (M M' : Matrix (Fin m) (Fin n) A) (h : p • M = p • M') : M.map φ = M'.map φ := by
  ext i j
  have := congrArg φ (congrFun (congrFun h i) j)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, hp, one_mul, Matrix.map_apply] using this

theorem lift_smul_eq_of_map {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A)
    (hker : ∀ z, φ z = 0 ↔ p * z = 0) (M M' : Matrix (Fin m) (Fin n) A) (h : M.map φ = M'.map φ) : p • M = p • M' := by
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at h2
  have h3 : φ (M i j - M' i j) = 0 := by rw [map_sub, h2, sub_self]
  rw [hker, mul_sub, sub_eq_zero] at h3
  simpa only [Matrix.smul_apply, smul_eq_mul] using h3

theorem lift_smul_conj {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • (β.1 * M * (β⁻¹).1) = β.1 * (p • M) * (β⁻¹).1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_smul_conj_inv {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • ((β⁻¹).1 * M * β.1) = (β⁻¹).1 * (p • M) * β.1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_conj_mul_smul {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M M' : Matrix (Fin n) (Fin n) A)
    (h : p • (M * M') = p • (1 : Matrix (Fin n) (Fin n) A)) :
    p • ((β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1)) = p • (1 : Matrix (Fin n) (Fin n) A) := by
  have e3 : (β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1) = β.1 * (M * M') * (β⁻¹).1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mul]
  rw [e3, lift_smul_conj, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

theorem lift_conj_part {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (g M : Matrix (Fin n) (Fin n) A)
    (h : p • g = p • (β.1 * M * (β⁻¹).1)) : p • ((β⁻¹).1 * g * β.1) = p • M := by
  rw [lift_smul_conj_inv, h, lift_smul_conj]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem lift_chart_idem {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) (he : toEAf D e * toEAf D e = toEAf D e) : φ (toEAf D e) = 1 := by
  have h0 : φ (1 - toEAf D e) = 0 := by
    rw [hker, mul_sub, mul_one, he, sub_self]
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem lift_chart_int {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hsurj : Function.Surjective φ) (h1 : φ (toEAf D e) = 1)
    (hint : ∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F)
    (o : GlobalTheory.SplitHecke.Ov D v) : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ (s : Formalism.IndefR.Lev.EAf D) = (o : Fv D.host.F v) := by
  obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
  refine ⟨⟨toEAf D e * z, (hint z).2 (hz ▸ o.2)⟩, ?_⟩
  show φ (toEAf D e * z) = _
  rw [map_mul, h1, one_mul, hz]

theorem lift_frG_one {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) :
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG T βT 1 = 1 := by
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
  rw [map_one, mul_one, inv_mul_cancel]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_St_of_part_inv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ) (hΛ : HatSelfDual σ J Λ)
    (p : Formalism.L2.Herm.intAf F E) (hq : Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p ∈ Formalism.L2.Herm.intAf F E)
    (Y Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hmm : (p : E ⊗[F] Formalism.L2.Herm.Af F) • ((β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) *
      (β.1 * Y'.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) = (p : E ⊗[F] Formalism.L2.Herm.Af F) • 1)
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Formalism.L2.Herm.Af F))
    (f : E ⊗[F] Formalism.L2.Herm.Af F) (hf : f = p + Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p) (hs : f • (g.1 - 1) = g.1 - 1)
    (hY : (p : E ⊗[F] Formalism.L2.Herm.Af F) • g.1 =
      (p : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) : g ∈ St β := by
  subst hf
  exact (mem_St_iff β Λ hβ g).2 (stab_of_part _ _ _ hΛ p.2 hq g hg hs _ _ (frame_mulVec β Λ hβ Y)
    (frame_mulVec β Λ hβ Y') hmm hY)

end Gen

set_option maxHeartbeats 1000000 in

theorem exists_supp_lift_adj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  intro D S T βS βT e PP v φ ι he hL Λ N hB h
  obtain ⟨hsurj, hker, hint, hres⟩ := hL
  have := PP.isPrime
  obtain ⟨p, hp, hpp, hres1⟩ := exists_idem_int he
  have hpe : toEAf D e = (p : Formalism.IndefR.Lev.EAf D) := hp.symm
  have hpp' : toEAf D e * toEAf D e = toEAf D e := by rw [hpe]; exact congrArg Subtype.val hpp
  have hp1 : φ (p : Formalism.IndefR.Lev.EAf D) = 1 := hpe ▸ lift_chart_idem hker hpp'
  have hker' : ∀ z, φ z = 0 ↔ (p : Formalism.IndefR.Lev.EAf D) * z = 0 := fun z => hpe ▸ hker z
  choose lf hlf using lift_chart_int hsurj (hpe ▸ hp1) hint
  set Y : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := h.val.map lf with hYdef
  set Y' : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := (h⁻¹).val.map lf with hY'def
  have hY : (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hY' : (Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      (h⁻¹).val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hYY : (p : Formalism.IndefR.Lev.EAf D) • (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = (p : Formalism.IndefR.Lev.EAf D) • 1 := by
    refine lift_smul_eq_of_map φ _ hker' _ _ ?_
    rw [Matrix.map_mul, hY, hY', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hmm := lift_conj_mul_smul βS _ _ _ hYY
  have hmm' := hmm
  rw [hp] at hmm'
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin S he.1 _ _ hmm'
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S
  have hsf := supp_fin S (f := e + cA D e) hs
  have hκ' : (p : Formalism.IndefR.Lev.EAf D) • (finE S κ).1 =
      (p : Formalism.IndefR.Lev.EAf D) • (βS.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (βS⁻¹).1) := by
    rw [hp]; exact hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE S κ ∈ St βS :=
    mem_St_of_part_inv D.sp.cm.sig S.gram Λ βS hB.1 (hatL_selfDual hB) p (sigR_int p.2) Y Y' hmm (finE S κ)
      (finE_mem_UA S κ) _ hf hsf hκ'
  refine ⟨κ, hs, (T3 PP e _ hP).2.2.1 κ hs, hSt, ?_, fun P' h1 h2 => ?_, fun x => ?_⟩
  · rw [redFn_of_smul_eq βS PP _ hSt p hres1 Y hκ']
    ext i j
    simp only [Matrix.map_apply]
    exact hres (lf (h.val i j)) (h.val i j) (hlf _).symm
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one βS P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · have hG : (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG S βS κ).val.map φ =
        h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
      rw [← hY]
      refine lift_map_eq_of_smul φ _ hp1 _ _ ?_
      unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
      rw [Units.val_mul, Units.val_mul]
      exact lift_conj_part βS _ _ _ hκ'
    unfold rdAdj
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_actO, lift_frG_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.map_mul, hG]

end GlobalTheory.DownLift.SplitCoef
