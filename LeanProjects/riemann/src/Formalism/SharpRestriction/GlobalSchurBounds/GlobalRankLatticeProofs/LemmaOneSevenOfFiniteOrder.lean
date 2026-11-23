import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UnitaryKronecker

noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

section Gen

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K]

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs x hx y hy => hi ?_⟩
  exact TotallyDisconnectedSpace.isTotallyDisconnected_univ (f '' s) (Set.subset_univ _)
    (hs.image f hf.continuousOn) (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy)

theorem tens_finite :
    letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
    Module.Finite K (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  exact Module.Finite.equiv (R := K) (M := K ⊗[F] E) (N := E ⊗[F] K)
      { (TensorProduct.comm F K E) with
        map_smul' := fun c x => by
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a e =>
            simp [Algebra.smul_def, TensorProduct.smul_tmul']
            rw [show algebraMap K (E ⊗[F] K) c = (1 : E) ⊗ₜ[F] c from rfl,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          | add x y hx hy => simp_all [smul_add] }

theorem tens_topRing :
    letI := tensTop (F := F) (E := E) K
    IsTopologicalRing (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing K (E ⊗[F] K)

theorem tens_td [TotallyDisconnectedSpace K] :
    letI := tensTop (F := F) (E := E) K
    TotallyDisconnectedSpace (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  let e := (Module.finBasis K (E ⊗[F] K)).equivFun
  exact td_of_inj e (IsModuleTopology.continuous_of_linearMap e.toLinearMap) e.injective

end Gen

section Steps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {k : ℕ}

theorem inclE_injective (R : Type) [Field R] [Algebra F R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  exact (inclE (F := F) (E := E) R).injective

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (ι := Fin k) φ) := by
  intro x y hxy
  apply Units.ext
  ext i j
  have h := congrArg (fun z : GL (Fin k) B => (z : Matrix (Fin k) (Fin k) B) i j) hxy
  simpa [bc, hφ.eq_iff] using h

theorem bc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (x : GL (Fin k) A) : bc ψ (bc φ x) = bc (ψ.comp φ) x := by
  apply Units.ext
  ext i j
  simp [bc]

theorem prV_inclE [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) =
      inclE (F := F) (E := E) (v.adicCompletion F) := by
  ext x
  simp [prV, inclE]

theorem gl_topGroup {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    IsTopologicalGroup (GL (Fin k) T) := inferInstance

theorem gl_td {T : Type} [CommRing T] [TopologicalSpace T] [TotallyDisconnectedSpace T] :
    TotallyDisconnectedSpace (GL (Fin k) T) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin k) (Fin k) T) :=
    (inferInstance : TotallyDisconnectedSpace (Fin k → Fin k → T))
  exact td_of_inj (fun x : GL (Fin k) T => (x : Matrix (Fin k) (Fin k) T)) Units.continuous_val
    (fun a b hab => Units.ext hab)

theorem proG_order {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] (g : ℕ) (hg : g.Prime) (Uw : Subgroup G) (h : IsProG g Uw)
    (x : G) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) : ∃ m : ℕ, orderOf x = g ^ m := by
  classical
  obtain ⟨hc, hidx⟩ := h
  haveI : CompactSpace Uw := isCompact_iff_compactSpace.mp hc
  haveI : T1Space Uw := inferInstance
  let xu : Uw := ⟨x, hx⟩
  have hxu : orderOf xu = orderOf x := by
    exact Subgroup.orderOf_mk x hx
  have hnpos : 0 < orderOf x := hfin.orderOf_pos
  let Z : Finset Uw := (Finset.Ioo 0 (orderOf x)).image (fun j => xu ^ j)
  have hZ : IsOpen ((↑Z : Set Uw)ᶜ) := (Z.finite_toSet.isClosed).isOpen_compl
  have h1 : (1 : Uw) ∈ (↑Z : Set Uw)ᶜ := by
    intro hm
    obtain ⟨j, hj, hj1⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hm)
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.1 hj
    have := orderOf_le_of_pow_eq_one hj0 hj1
    omega
  obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup Uw, (N : Set Uw) ⊆ (↑Z : Set Uw)ᶜ := by
    haveI : T2Space Uw := inferInstance
    obtain ⟨H, hH⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := ProfiniteGrp.of Uw) hZ h1
    exact ⟨H, hH⟩
  haveI hNn : N.toSubgroup.Normal := N.isNormal'
  obtain ⟨m, hm⟩ := hidx N.toSubgroup N.isOpen' hNn
  have hpow : xu ^ (g ^ m) ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hm]
    exact pow_card_eq_one'
  have hdvd : orderOf x ∣ g ^ m := by
    by_contra hnd
    have hj0 : 0 < g ^ m % orderOf x :=
      Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have hjn : g ^ m % orderOf x < orderOf x := Nat.mod_lt _ hnpos
    have hmem : xu ^ (g ^ m % orderOf x) ∈ N.toSubgroup := by
      rw [← hxu, pow_mod_orderOf]
      exact hpow
    have hZm : xu ^ (g ^ m % orderOf x) ∈ (↑Z : Set Uw) :=
      Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, Finset.mem_Ioo.2 ⟨hj0, hjn⟩, rfl⟩)
    exact hN hmem hZm
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  exact ⟨i, hi⟩

theorem step_pro {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (g : ℕ) (hg : g.Prime) (Uw : Subgroup (GL (Fin k) T))
    (h : IsProG g Uw) (x : GL (Fin k) T) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) :
    ∃ m : ℕ, orderOf x = g ^ m := by
  haveI := gl_topGroup (k := k) (T := T)
  haveI := gl_td (k := k) (T := T)
  exact proG_order g hg Uw h x hx hfin

end Steps

def DefiniteUnitaryFiniteOrder (D : D7) : Prop :=
  ∀ σ : D.host.E →ₐ[D.host.F] D.host.E, (∀ x, σ x = D.host.conj x) →
  ∀ J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E, IsHerm (σ : D.host.E →+* D.host.E) J → IsDef σ J →
  letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  ∀ U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
  ∀ γ ∈ UJ (σ : D.host.E →+* D.host.E) J,
    bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∈
      U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

set_option maxHeartbeats 1000000 in
theorem finiteModel_of_heckeEstimate (D : D7) (hF : DefiniteUnitaryFiniteOrder D) : division_rows_rational_lattice D := by
  intro σ hσ J hJ hD g hg hlt v hv U hU hUc _hUo Uw hUw hUUw y hy
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx1
  have hfin : IsOfFinOrder γ := hF σ hσ J hJ hD U hU hUc y hy γ hγ hx2
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx2
  have hcomp : bc (prV v) (bc (inclE (F := D.host.F) (E := D.host.E)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ) =
      bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ := by
    rw [bc_comp, prV_inclE]
  have hordγ : orderOf (bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ)
      = orderOf γ :=
    orderOf_injective (bc (ι := Fin D.R.k) (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)))
      (bc_injective _ (inclE_injective (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))) γ
  have hconj : bc (prV v) ((MulAut.conj y).toMonoidHom u) =
      MulAut.conj (bc (prV v) y) (bc (prV v) u) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hord_u : orderOf (bc (prV v) u) = orderOf γ := by
    have e1 := MulEquiv.orderOf_eq (MulAut.conj (bc (prV v) y)) (bc (prV v) u)
    have e2 := congrArg (fun z => orderOf (bc (prV v) z)) hux
    have e3 := congrArg orderOf hcomp
    rw [← e1, ← hconj, e2, e3, hordγ]
  have hfin' : IsOfFinOrder (bc (prV v) u) := by
    rw [← orderOf_pos_iff, hord_u]
    exact hfin.orderOf_pos
  obtain ⟨m, hm⟩ := @step_pro D.R.k _ _
    (tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))
    (tens_topRing (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    (tens_td (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    g hg Uw hUw (bc (prV v) u) (hUUw u hu) hfin'
  rw [hord_u] at hm
  have hlt' : 4 * D.R.ord * D.R.k < g - 1 := by
    have h2 : 2 * D.R.f * D.R.k = 4 * D.R.ord * D.R.k := by
      have hf : D.R.f = 2 * D.R.ord := rfl
      rw [hf]
      ring
    omega
  have hΓ := Formalism.HC.HostAx.hostStab D.host.toHostAx D.R.k g hg hlt' (Subgroup.zpowers γ) (by
      intro δ hδ
      have hd : orderOf δ ∣ g ^ m := hm ▸ orderOf_dvd_of_mem_zpowers hδ
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hd
      exact ⟨i, hi⟩)
  have h1 : γ = 1 := by
    have hm' : γ ∈ Subgroup.zpowers γ := Subgroup.mem_zpowers γ
    rw [hΓ] at hm'
    exact Subgroup.mem_bot.mp hm'
  rw [h1, map_one]

theorem totReal_emb {F : Type} [Field F] [IsTotallyReal F] (φ : F →+* ℂ) :
    ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ) := by
  have h : NumberField.ComplexEmbedding.IsReal φ := by
    exact NumberField.IsTotallyReal.complexEmbedding_isReal φ
  exact ⟨h.embedding, fun x => (h.coe_embedding_apply x).symm⟩

theorem finite_order_of_totally_real (hG : Formalism.MainNotions.Ext.FinOrdG) (D : D7) : DefiniteUnitaryFiniteOrder D := by
  intro σ _ J hJ hD U hU hUc y hy γ hγ hmem
  exact hG D.host.F D.host.E (fun φ => totReal_emb φ) σ D.R.k J hJ hD U hU hUc y hy γ hγ hmem

end Formalism.MainNotions.UnusedSlot33
