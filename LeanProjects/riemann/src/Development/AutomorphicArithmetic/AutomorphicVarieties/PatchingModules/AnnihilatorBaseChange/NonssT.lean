import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ClosureBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.IsProLOfPL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChBarPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.GensImg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem fg_image {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (p : A →* B) (hc : Continuous p) (hs : Function.Surjective p)
    (h : ∃ s : Finset A, (Subgroup.closure (s : Set A)).topologicalClosure = ⊤) :
    ∃ s : Finset B, (Subgroup.closure (s : Set B)).topologicalClosure = ⊤ := by
  obtain ⟨s, hsd⟩ := h
  classical
  refine ⟨s.image p, ?_⟩
  rw [eq_top_iff]
  intro b _
  obtain ⟨a, rfl⟩ := hs b
  have ha : a ∈ closure ((Subgroup.closure (s : Set A) : Subgroup A) : Set A) := by
    rw [← Subgroup.topologicalClosure_coe, hsd]
    trivial
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, Finset.coe_image, ← MonoidHom.map_closure,
    Subgroup.coe_map]
  exact image_closure_subset_closure_image hc ⟨a, ha, rfl⟩

set_option maxHeartbeats 200000 in
private theorem co_local {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') : IsLocalHom f.toRingHom := by
  haveI := IsCO.toIsLocalRing O (R := R)
  haveI := IsCO.toIsLocalRing O (R := R')
  haveI : IsLocalHom (algebraMap O R') := IsCO.isLocalHom
  constructor
  intro x hx
  by_contra hnx
  obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) (f x)
  have hcu : IsUnit c := by
    by_contra hcn
    have h1 : algebraMap O R' c ∈ maximalIdeal R' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hcn (isUnit_of_map_unit (algebraMap O R') c h)
    have h2 := Ideal.add_mem _ hc h1
    rw [sub_add_cancel, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2 hx
  have hu : IsUnit (x - algebraMap O R c) := by
    have hxm : x ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnx
    have hcu' : IsUnit (algebraMap O R c) := hcu.map _
    by_contra hn
    have h2 : x - algebraMap O R c ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have h3 := Ideal.sub_mem _ hxm h2
    rw [sub_sub_cancel, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h3
    exact h3 hcu'
  have hfu := hu.map f
  rw [map_sub, AlgHom.commutes] at hfu
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc
  exact hc hfu

theorem UpperTheory.V.Pa.Core.nonssT :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → T.ProL → Adapted T (r := r) → 1 ≤ n → ∀ (Bh : Type) [CommRing Bh] (φ : (W.R ⧸ ii W) →+* Bh) (Q : Ideal Bh) (P : Ideal (Spo A)), Q.IsPrime → P.IsPrime → Q.comap φ = P.comap πb → NonSS (augmentationIdealKernel u) (RingHom.id B) (P.comap (algebraMap B (Spo A))) → NonSS (ooKer o) φ Q := by
  intro l _ L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m _ o πb hπ hT hA hn Bh _ φ Q P hQ hP hQP hN
  haveI : Finite (ResidueField O) := hO.finite
  haveI : CharP (ResidueField O) l := hO.char
  obtain ⟨⟨hco, hfr, hfin, -⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hA
  haveI : IsLocalRing (Spo A) := hco.toIsLocalRing
  haveI : IsNoetherianRing (Spo A) := hco.toIsNoetherian
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : IsLocalHom (algebraMap B (Spo A)) := Algebra.IsIntegral.isLocalHom B (Spo A)
  haveI : IsLocalHom πb.toRingHom := co_local πb
  obtain ⟨hfB, ⟨χ, h, hχ, hm⟩, hsp⟩ := BC.pair_mf l G0.frame O n r B u (BC.phi0 l L G0 T hT)
  obtain ⟨-, -, hsp'⟩ := BC.pair_mf l Λ.G.frame O n o.r' (W.R ⧸ ii W) o.p
    (phi_fg Λ.G.frame (fg_image Λ.πo Λ.πo_cont Λ.πo_surj Λ.fg))
  have h1 : NonSS (augmentationIdealKernel u) (algebraMap B (Spo A)) P := by
    refine BC.nonSS_field B B (Spo A) _ _ _ _ _ P hP (Ideal.comap_id _).symm ?_ hN
    obtain ⟨s, hs⟩ := hsp (pairGens u)
    exact ⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩
  have h2 : NonSS (ooKer o) πb.toRingHom P := by
    refine BC.nonSS_mono B (W.R ⧸ ii W) (Spo A) G0.G₀ Λ.G.G₀ Λ.h.p₀ _ _ _ _ P Λ.h.p₀_surj (fun z hz => ?_) h1
    have hD : o.p.D.map πb.toRingHom = (u.D.map (algebraMap B (Spo A))).comap Λ.h.p₀ :=
      (ooMaps l L G0 T Λ n O r B u J D A W m o πb hπ).1.trans (GDet.ext fun _ _ _ _ => rfl)
    have h3 := chBarPush n (W.R ⧸ ii W) (Spo A) Λ.G.G₀ G0.G₀ πb.toRingHom Λ.h.p₀ o.p.D
      (u.D.map (algebraMap B (Spo A))) _ Λ.h.p₀_cont hD z hz
    refine BC.closure_bc n h B (Spo A) G0.G₀ u.D χ u.cont hχ hm (algebraMap B (Spo A)) (pairGens u) _ ?_ _ h3
    rintro _ ⟨y, hy, rfl⟩
    exact gensImg l L G0 T Λ n O r B u J D A W m o πb hπ hT hA hn y hy
  refine BC.nonSS_field (W.R ⧸ ii W) (Spo A) Bh _ _ _ φ P Q hQ hQP ?_ h2
  obtain ⟨s, hs⟩ := hsp' (pairGens o.p ∪ qGens (O := O) (F := Λ.G.frame) Λ.ph Λ.ta
    (fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i)) fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i))
  exact ⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩
