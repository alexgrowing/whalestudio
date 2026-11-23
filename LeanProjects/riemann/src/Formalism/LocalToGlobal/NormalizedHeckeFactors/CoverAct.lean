import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2.NCov

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {S : Set (End K V)} [IsLocalRing O]

theorem W_le_comap (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {t : End K V} (ht : t ∈ Algebra.adjoin O S)
    (χ : Algebra.adjoin O S → K) : W _ χ ≤ (W _ χ).comap t := by
  intro x hx
  refine (Submodule.mem_iInf _).2 fun u => ?_
  exact mapsTo_maxGenEigenspace_of_comm (commute_adjoin hS u.2 ht) (χ u) ((Submodule.mem_iInf _).1 hx u)

theorem part_le_comap (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {t : End K V} (ht : t ∈ Algebra.adjoin O S)
    (𝔪 : Ideal (Algebra.adjoin O S)) : part _ 𝔪 ≤ (part _ 𝔪).comap t :=
  iSup₂_le fun ψ hψ => (W_le_comap hS ht _).trans (Submodule.comap_mono
    (le_iSup₂_of_le (f := fun (ψ' : Algebra.adjoin O S →ₐ[O] O) (_ : cls ψ' = 𝔪) => W _ (pt ψ')) ψ hψ le_rfl))

theorem off_le_comap (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {t : End K V} (ht : t ∈ Algebra.adjoin O S)
    (𝔪 : Ideal (Algebra.adjoin O S)) : off _ 𝔪 ≤ (off _ 𝔪).comap t :=
  iSup₂_le fun ψ hψ => (W_le_comap hS ht _).trans (Submodule.comap_mono
    (le_iSup₂_of_le (f := fun (ψ' : Algebra.adjoin O S →ₐ[O] O) (_ : cls ψ' ≠ 𝔪) => W _ (pt ψ')) ψ hψ le_rfl))

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def SplitEx (D : D7) : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

theorem hecke_transport {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m)
    (e : D.what₂.MtL μ j = D.what₂.MtL μ' j') (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (x x' : D.what₂.MtL μ j) :
    (M μ' j' b1 b2).real (D.what₂.jMt μ' j' (cast e x')) =
        NG.tN (M μ' j' b1 b2).J s ϖ k ((M μ' j' b1 b2).real (D.what₂.jMt μ' j' (cast e x))) ↔
      (M μ j a1 a2).real (D.what₂.jMt μ j x') =
        NG.tN (M μ j a1 a2).J s ϖ k ((M μ j a1 a2).real (D.what₂.jMt μ j x)) := by
  subst hμ hj
  simp only [cast_eq]

theorem psiAct_of (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (HT : HeckeTied D M) (hex : SplitEx D) :
    PsiAct T := by
  intro j w i h v k hvk
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem j w i).1 h
  have h1 : 1 ≤ j := e1 ▸ (D.nd.j_range i).1
  have h2 : j ≤ D.R.m := e1 ▸ (D.nd.j_range i).2
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, -, -⟩ := gens_hypsTw T.B hstd h1 h2 (locPl_of_mem D h)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  have hdisj := NCov.disjoint_part_off hinj hS (T.mx j w i)
  have hmem : T.B.hK j w v k ∈ heckeAlg T.B j w := Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩
  obtain ⟨hso, hk1, hk2⟩ := (genAt_iff T h v k).2 hvk
  obtain ⟨s, ϖ, hconj, hunif⟩ := hex v hso.1
  set A := (D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))
  let F1 := (T.Psi j w i h).comp A
  let F2 := (T.B.hK j w v k).comp (T.Psi j w i h)
  suffices hall : LinearMap.eqLocus F1 F2 = ⊤ by
    intro z
    have hz : z ∈ LinearMap.eqLocus F1 F2 := by rw [hall]; exact Submodule.mem_top
    exact LinearMap.mem_eqLocus.1 hz
  rw [eq_top_iff, ← D.nd.prMt_span i, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  show T.Psi j w i h (A (D.nd.prMt i x)) = T.B.hK j w v k (T.Psi j w i h (D.nd.prMt i x))
  set x' := castMtInv D h (T.B.hL j w v k (castMt D h x))
  have hμ : D.nd.mu i = D.what₂.muTw w := by rw [D.nd.mu_w i, e2]
  have hdef := T.B.hL_def j w h1 h2 v k s ϖ hvk hconj hunif (castMt D h x)
  have hx' : castMt D h x' = T.B.hL j w v k (castMt D h x) := castMt_castMtInv D h _
  rw [← hx'] at hdef
  have hrec := (hecke_transport (M := M) hμ e1 (D.nd.j_range i).1 (D.nd.j_range i).2 h1 h2 (mtL_eq D h) s ϖ k
    x x').1 hdef
  have hA : D.nd.prMt i x' = A (D.nd.prMt i x) :=
    HT.hT i v k s ϖ hso hconj hunif hk1 hk2 x x' hrec
  rw [← hA]

  have hp1 : T.Psi j w i h (D.nd.prMt i x') ∈ NCov.part (heckeAlg T.B j w) (T.mx j w i) :=
    (T.Psi_range j w i h _).2 ⟨_, rfl⟩
  have hp2 : T.B.hK j w v k (T.Psi j w i h (D.nd.prMt i x)) ∈ NCov.part (heckeAlg T.B j w) (T.mx j w i) :=
    NCov.part_le_comap hS hmem _ ((T.Psi_range j w i h _).2 ⟨_, rfl⟩)
  have ho1 := T.Psi_pr j w i h x'
  have ho2 : T.B.hK j w v k (T.Psi j w i h (D.nd.prMt i x) - T.B.iV j w (castMt D h x)) ∈
      NCov.off (heckeAlg T.B j w) (T.mx j w i) :=
    NCov.off_le_comap hS hmem _ (T.Psi_pr j w i h x)
  rw [hx', ← T.B.hK_def] at ho1
  rw [map_sub] at ho2
  have hd : T.Psi j w i h (D.nd.prMt i x') - T.B.hK j w v k (T.Psi j w i h (D.nd.prMt i x)) ∈
      NCov.off (heckeAlg T.B j w) (T.mx j w i) := by
    have := Submodule.sub_mem _ ho1 ho2
    rwa [sub_sub_sub_cancel_right] at this
  have hz := Submodule.disjoint_def.1 hdisj _ (Submodule.sub_mem _ hp1 hp2) hd
  exact sub_eq_zero.1 hz

theorem etaC_goodPts_eq_etaJ_of (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (HT : HeckeTied D M) (hex : SplitEx D)
    {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaC T.B j w (goodPts T j w) = D.what₂.etaJ j w :=
  etaC_goodPts_eq_etaJ T hstd (psiAct_of T hstd HT hex) h1 h2 hw

def etaN (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl) : ℚ := etaC T.B j w (goodPts T j w)

theorem etaN_eq_etaJ (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (HT : HeckeTied D M) (hex : SplitEx D)
    {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaN T j w = D.what₂.etaJ j w := etaC_goodPts_eq_etaJ_of T hstd HT hex h1 h2 hw

end Formalism.L2
