import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CongAtIdem

theorem read_rel {A B K E : Type} [CommRing A] [CommRing B] [CommRing K] [CommRing E] {m n : Type} [Fintype m] [Fintype n]
    (t : A →+* B) (φ : B →+* K) (i : E →+* A) (j : E →+* B) (hij : ∀ x, t (i x) = j x) {e : A} (he : φ (t e) = 1)
    (X : Matrix m m A) (Z : Matrix n n A) (γ γ₀ : Matrix m n E) (v : Matrix m n A) (k : ℕ)
    (h : γ₀.map (fun r => e * i r) = X * γ.map (fun r => e * i r) * Z + k • v) (r : m) (s : n) :
    φ ((X.map t * γ.map j * Z.map t - γ₀.map j) r s) = -((k : K) * φ (t (v r s))) := by
  have h1 := congrArg (fun W : Matrix m n A => φ (t (W r s))) h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, map_add, map_sum, map_mul, he,
    one_mul, hij, nsmul_eq_mul, map_natCast] at h1
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, h1]
  ring

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem adAt_toEAf_of_isIdemAt {f : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hf : Formalism.L2.NTheta.IsIdemAt f P) : adAt D.host.F P (toEAf D f) = 1 := by
  let ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x =>
    afIso_tmul_one D.host.F D.host.E x
  have h2 : ∀ y, y ∈ intAE D ↔ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y Q) ≤ 1 := fun y =>
    (GlobalTheory.IdemSupport.mem_intAE_iff y).trans (mem_rInt_iff D.host.F D.host.E _)
  exact GlobalTheory.ChrOff.comp_idem ι h1 h2 hf

theorem adAt_toEAf_of_isIdemSum {e : AE D} {Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (he : IsIdemSum e Ps) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Ps) :
    adAt D.host.F P (toEAf D e) = 1 := by
  obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
  have h := congrArg (fun z => adAt D.host.F P (toEAf D z)) hae
  simp only [map_mul, adAt_toEAf_of_isIdemAt ha, one_mul] at h
  exact h

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem isIntegral_of_eq {x : D.host.E} (h : ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = x) :
    IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := h
  exact r.2

theorem tmul_one_mem_rInt {x : D.host.E} (hx : IsIntegral ℤ x) :
    x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩)

theorem one_tmul_mem_rInt {α : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (hα : α ∈ intAf D.host.F) :
    (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)

theorem exists_den_stdHom (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s,
    ((d : EF D) * toEAf D (v r s) : Formalism.L2.DIV.AfE D.host.F D.host.E) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (insert ((a0 : D.host.E))⁻¹ (Finset.image (fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2) Finset.univ))
  have hx0 : IsIntegral ℤ ((d : D.host.E) * ((a0 : D.host.E))⁻¹) := by
    rw [← nsmul_eq_mul]; exact isIntegral_of_eq (hint _ (Finset.mem_insert_self _ _))
  have hG : ∀ k j, IsIntegral ℤ ((d : D.host.E) * S.gram k j) := fun k j => by
    rw [← nsmul_eq_mul]
    exact isIntegral_of_eq (hint _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)))
  refine ⟨d * d, Nat.mul_pos hd hd, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        refine isIntegral_of_eq ⟨y, ?_⟩
        rw [hy, Algebra.smul_def]
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((d : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul
          ((hs k).map (starRingEnd D.host.E).toIntAlgHom) (hG k c)
      have e : ((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) = (d : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * d * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e]
      exact ((hx0.mul hA).mul (ht r)).mul hsum
    change ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) ∈ _
    have e3 : ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) =
        ((((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) ⊗ₜ[D.host.F]
          (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      have hc : ((d * d : ℕ) : EF D) = ((d * d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
        (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
          (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d * d)).symm
      rw [hc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e3]
    exact mul_mem (tmul_one_mem_rInt hint') (one_tmul_mem_rInt hα)
  | zero => intro r s; simp
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, RingHom.map_add (toEAf D), mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, RingHom.map_neg (toEAf D), mul_neg]; exact neg_mem (hx r s)

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem finM_rfl (V : HSp D) (x : GA D V) : finM V rfl x = (Formalism.L2.Theta.mt V x).map (toEAf D) := by
  simp [finM, finCongr_refl]

theorem mt_mul' (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem inv_val_eq (V : HSp D) (x : GA D V) (Y : GL (Fin V.rank) (EF D)) (hY : finM V rfl x = Y.1) :
    (Y⁻¹ : GL (Fin V.rank) (EF D)).1 = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
  have h1 : (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1 = 1 := by
    rw [← hY, finM_rfl, ← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one',
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc (Y⁻¹ : GL (Fin V.rank) (EF D)).1
      = ((Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1) * (Y⁻¹ : GL (Fin V.rank) (EF D)).1 := by
        rw [h1, Matrix.one_mul]
    _ = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

theorem cong_at_idem : ∀ {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (e : AE D)
    (Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e Ps → ∃ d : ℕ, 0 < d ∧
    ∀ (g : GA D S) (h : GA D T) (Y : GL (Fin a) (EF D)) (Y' : GL (Fin b) (EF D)), finM S hS g = Y.1 → finM T hT h = Y'.1 →
    ∀ (M : ℕ) (γ γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T →
      γ₀.map (fun r => e * incA D r) = actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r) + (d * M) • v →
      ∀ P ∈ Ps, ∀ r s, Valued.v (adAt D.host.F P
        ((HMul.hMul (HMul.hMul ((Y'⁻¹ : GL (Fin b) (EF D)).1 : Matrix (Fin b) (Fin b) (EF D))
          (((LinearMap.toMatrix' (toHom S T hS hT γ)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))))
          (Y.1 : Matrix (Fin a) (Fin a) (EF D)) -
          ((LinearMap.toMatrix' (toHom S T hS hT γ₀)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))) r s)) ≤
        Valued.v ((M : ℕ) : P.adicCompletion D.host.E) := by
  intro D S T a b hS hT e Ps he
  subst hS; subst hT
  obtain ⟨d, hd, hden⟩ := exists_den_stdHom S T
  refine ⟨d, hd, ?_⟩
  intro g h Y Y' hY hY' M γ γ₀ v hv hH P hP r s
  rw [← hY, finM_rfl, inv_val_eq T h Y' hY']
  simp only [toHom, LinearMap.toMatrix'_toLin', finCongr_refl, Matrix.reindex_refl_refl]
  rw [actO, inv_inv] at hH
  have key := read_rel (toEAf D) (adAt D.host.F P) (incA D)
    (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (fun _ => rfl)
    (adAt_toEAf_of_isIdemSum he hP) _ _ γ γ₀ v (d * M) hH r s
  have hint : Valued.v (adAt D.host.F P ((d : EF D) * toEAf D (v r s))) ≤ 1 :=
    (mem_rInt_iff D.host.F D.host.E _).1 (hden v hv r s) P
  rw [RingHom.map_mul, map_natCast (adAt D.host.F P)] at hint
  refine (congrArg Valued.v key).trans_le ?_
  rw [Valuation.map_neg, Nat.cast_mul, mul_right_comm, Valuation.map_mul]
  exact mul_le_of_le_one_left' hint

end GlobalTheory.AdForm.CongAtIdem
