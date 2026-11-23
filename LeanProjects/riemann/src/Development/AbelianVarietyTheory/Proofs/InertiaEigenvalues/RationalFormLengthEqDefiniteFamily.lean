import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩

open scoped Formalism.L2.Col in

theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = Formalism.L2.Col.lenUW w A B := by
  unfold Formalism.L2.Col.lenUW Formalism.L2.Col.lenW
  rw [Formalism.L2.Col.atW_map, Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j
      rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := GlobalTheory.T.concreteProjector_eq_orthogonalProjection D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
