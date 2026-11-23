import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebungStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveWithCotangentOfDualHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmulStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R where
  counit_eq_zero x hx := by
    have hle : kerIdeal f ≤ augIdeal R A := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [CoalgHomClass.counit_comp_apply] using hc'
    simpa using hle hx
  map_mkQ_comul_eq_zero := by
    intro x hx
    let Q := A ⧸ kerIdeal f
    let q := Ideal.Quotient.mkₐ R (kerIdeal f)
    let Φ : A →ₐ[R] Q ⊗[R] Q := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A)
    have hqf : ∀ c : C, q (f c) = algebraMap R Q (counit (R := R) c) := by
      intro c
      have hmem : f (c - algebraMap R C (counit (R := R) c)) ∈ kerIdeal f := by
        refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : q (f (c - algebraMap R C (counit (R := R) c))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0
    have hg : q.toLinearMap ∘ₗ (f : C →ₗ[R] A) = Algebra.linearMap R Q ∘ₗ counit :=
      LinearMap.ext hqf
    have hΦ : kerIdeal f ≤ RingHom.ker Φ := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
      rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
        hg]
      have hsplit : TensorProduct.map (Algebra.linearMap R Q ∘ₗ counit)
          (Algebra.linearMap R Q ∘ₗ counit) =
          TensorProduct.map (Algebra.linearMap R Q) (Algebra.linearMap R Q ∘ₗ counit) ∘ₗ
            LinearMap.rTensor C (counit (R := R) (A := C)) := by
        rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
      rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
      simp [hc']
    exact hΦ hx
  antipode_mem := by
    have h0 : ((1 : WithConv (A →ₐ[R] A)).ofConv).comp (f : C →ₐ[R] A) =
        (1 : WithConv (C →ₐ[R] A)).ofConv := by
      ext c
      simp [CoalgHomClass.counit_comp_apply]
    have h1 : WithConv.toConv ((HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A)) *
        WithConv.toConv (f : C →ₐ[R] A) = 1 := by
      have := AlgHom.convMul_comp_bialgHom_distrib
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom R A)) (WithConv.toConv (AlgHom.id R A)) f
      rw [AlgHom.antipode_id_cancel, h0] at this
      apply WithConv.ofConv_injective
      rw [this]
      rfl
    have h2 : (HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A) =
        (f : C →ₐ[R] A).comp (HopfAlgebra.antipodeAlgHom R C) :=
      congrArg WithConv.ofConv (eq_inv_of_mul_eq_one_left h1)
    have hS : ∀ c : C, HopfAlgebra.antipode R (f c) = f (HopfAlgebra.antipode R c) := fun c => by
      simpa using DFunLike.congr_fun h2 c
    have hle : kerIdeal f ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom R A) (kerIdeal f) := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hc' : counit (R := R) c = 0 := by simpa using hc
      change HopfAlgebra.antipode R (f c) ∈ kerIdeal f
      rw [hS]
      refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
      rw [RingHom.mem_ker]
      simpa using hc'
    intro x hx
    exact hle hx

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    set V := (verschiebung h G).app 1 with hV
    set F := (relFrob h G).app 1 with hF
    set J : Ideal ((frobTwist h G).A 1) := kerIdeal V with hJdef
    haveI hJ : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπa : ∀ a, π a = Ideal.Quotient.mk J a := fun a => rfl
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    haveI : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    haveI : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ
    have hJaug : ∀ x ∈ J, counit (R := K) x = 0 := fun x hx =>
      Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars K) hx

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) := by
      intro a
      have hmem : V (a - algebraMap K (G.A 1) (counit (R := K) a)) ∈ J := by
        refine Ideal.mem_map_of_mem (V : G.A 1 →ₐ[K] (frobTwist h G).A 1) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : π (V (a - algebraMap K (G.A 1) (counit (R := K) a))) = 0 := by
        rw [hπa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ := GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      intro a ha
      have haJ : a ∈ J := by
        rw [RingHom.mem_ker, hπa] at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      rw [RingHom.mem_ker]
      exact GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K (frobTwist h G) G (verschiebung h G) (relFrob h G)
        (relFrob_comp_verschiebung h G) a haJ
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    have hrange : ∀ x : Cot K ((frobTwist h G).A 1), cotMap π x = 0 →
        x ∈ LinearMap.range (cotMap V) := by
      let Rg := LinearMap.range (cotMap V)
      let D₀ : (frobTwist h G).A 1 →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        Rg.mkQ ∘ₗ AugCot.d (counitAlgHom K ((frobTwist h G).A 1))
      have hD₀ : ∀ a, D₀ a = Rg.mkQ (dUnit K a) := fun a => rfl
      have hD₀mul : ∀ a b, D₀ (a * b) =
          counit (R := K) a • D₀ b + counit (R := K) b • D₀ a := by
        intro a b
        rw [hD₀, hD₀, hD₀]
        change Rg.mkQ (AugCot.d _ (a * b)) =
          counit (R := K) a • Rg.mkQ (AugCot.d _ b) + counit (R := K) b • Rg.mkQ (AugCot.d _ a)
        rw [AugCot.d_mul]
        simp
      have hJD : ∀ x ∈ J, D₀ x = 0 := by
        intro x hx
        refine Submodule.span_induction (p := fun x _ => D₀ x = 0) ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨c, hc, rfl⟩
          rw [hD₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨dUnit K c, cotMap_d V c⟩
        · exact map_zero D₀
        · intro u v _ _ hu hv
          rw [map_add, hu, hv, add_zero]
        · intro a u hu hu0
          rw [smul_eq_mul, hD₀mul, hu0, hJaug u hu, zero_smul, smul_zero, add_zero]
      let D : ((frobTwist h G).A 1 ⧸ J) →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        (J.restrictScalars K).liftQ D₀ (fun x hx => hJD x hx) ∘ₗ
          (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
      have hD : ∀ a, D (Ideal.Quotient.mk J a) = D₀ a := fun a => rfl
      have hDmul : ∀ u v, D (u * v) = counit (R := K) u • D v + counit (R := K) v • D u := by
        intro u v
        obtain ⟨a, rfl⟩ := hπ u
        obtain ⟨b, rfl⟩ := hπ v
        rw [← map_mul, hπa, hπa, hπa, hD, hD, hD, hD₀mul]
        rfl
      let L := AugCot.lift (counitAlgHom K ((frobTwist h G).A 1 ⧸ J)) D
        (fun u v => by simpa using hDmul u v)
      have hL : L ∘ₗ cotMap π = Rg.mkQ := by
        apply AugCot.hom_ext
        intro a
        rw [LinearMap.comp_apply]
        change L (cotMap π (dUnit K a)) = Rg.mkQ (dUnit K a)
        rw [cotMap_d]
        change L (AugCot.d _ (π a)) = _
        rw [AugCot.lift_d, hπa, hD, hD₀]
      intro x hx
      have := congrArg (fun g => g x) hL
      simp only [LinearMap.comp_apply, hx, map_zero] at this
      exact (Submodule.Quotient.mk_eq_zero Rg).mp this.symm
    obtain ⟨w', hw'⟩ := hrange (dUnit K β - w) (by rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
