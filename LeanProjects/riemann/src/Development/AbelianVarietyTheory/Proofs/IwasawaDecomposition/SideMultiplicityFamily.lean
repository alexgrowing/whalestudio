import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.FitHecke

section NC
open Formalism.L2.NCov Module Module.End

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] {S : Set (End K V)}

theorem disjoint_part_off (hinj : Function.Injective (algebraMap O K)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (𝔪 : Ideal (Algebra.adjoin O S)) :
    Disjoint (part (Algebra.adjoin O S) 𝔪) (off (Algebra.adjoin O S) 𝔪) :=
  ((iSupIndep_alt (O := O) hS).comp (pt_injective hinj)).disjoint_biSup_biSup
    (s := {ψ | cls ψ = 𝔪}) (t := {ψ | cls ψ ≠ 𝔪}) (Set.disjoint_left.2 fun _ h h' => h' h)

theorem W_mapsTo (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (χ : Algebra.adjoin O S → K) (t : Algebra.adjoin O S)
    {x : V} (hx : x ∈ W (Algebra.adjoin O S) χ) : (t : End K V) x ∈ W (Algebra.adjoin O S) χ := by
  unfold W at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro s
  exact mapsTo_maxGenEigenspace_of_comm (commute_adjoin hS s.2 t.2) (χ s) (hx s)

theorem off_mapsTo (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (𝔪 : Ideal (Algebra.adjoin O S)) (t : Algebra.adjoin O S)
    {y : V} (hy : y ∈ off (Algebra.adjoin O S) 𝔪) : (t : End K V) y ∈ off (Algebra.adjoin O S) 𝔪 := by
  have hle : off (Algebra.adjoin O S) 𝔪 ≤ (off (Algebra.adjoin O S) 𝔪).comap (t : End K V) := by
    refine iSup₂_le fun ψ hψ => ?_
    intro x hx
    exact (le_iSup₂ (f := fun (ψ : Algebra.adjoin O S →ₐ[O] O) (_ : cls ψ ≠ 𝔪) => W (Algebra.adjoin O S) (pt ψ)) ψ hψ)
      (W_mapsTo hS _ t hx)
  exact hle hy

theorem exists_unit_of_cls_ne (ψ ψ' : Algebra.adjoin O S →ₐ[O] O) (h : cls ψ ≠ cls ψ') :
    ∃ s, ∃ hs : s ∈ S, IsUnit (ψ ⟨s, Algebra.subset_adjoin hs⟩ - ψ' ⟨s, Algebra.subset_adjoin hs⟩) := by
  by_contra hne
  simp only [not_exists] at hne
  apply h
  have key : ∀ t : Algebra.adjoin O S, IsLocalRing.residue O (ψ t) = IsLocalRing.residue O (ψ' t) := by
    rintro ⟨t, ht⟩
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).2 (hne x hx)
    | algebraMap r =>
      have e : (⟨algebraMap O (End K V) r, Subalgebra.algebraMap_mem _ r⟩ : Algebra.adjoin O S) =
          algebraMap O (Algebra.adjoin O S) r := rfl
      rw [e, AlgHom.commutes, AlgHom.commutes]
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add, map_add, map_add, map_add, ihx, ihy]
    | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, map_mul, map_mul, map_mul, ihx, ihy]
  ext t
  simp only [cls, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, key t]

end NC

section Conj
variable {R : Ranks}

theorem conj_conj' (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

theorem isConjPl_symm' {H : Host R} {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj'])).symm

end Conj

section Gen
variable {D : D7} {M : MtFam D}

theorem jMt_inj' (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hb := (D.what₂.jMt_basis μ j b).1
  have : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) := hb.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  refine (injective_iff_map_eq_zero (D.what₂.jMt μ j)).2 fun y hy => ?_
  have hsum := b.sum_repr y
  rw [← hsum, map_sum] at hy
  simp only [LinearMap.map_smulₛₗ] at hy
  have hz := Fintype.linearIndependent_iff.1 hb _ hy
  rw [← hsum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [(map_eq_zero_iff _ D.what₂.embLL.injective).1 (hz a), zero_smul]

theorem hypOutside_transport' {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) :
    NG.HypOutside (M μ j a1 a2).J (M μ j a1 a2).χ B → NG.HypOutside (M μ' j' b1 b2).J (M μ' j' b1 b2).χ B := by
  subst hμ; subst hj; exact id

theorem mem_locs_self (i : D.nd.Loc) : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩

theorem genAt_of_splitOut (T : NormalizedLocalCompatibility D M) {i : D.nd.Loc} {v : PlE D.host} {k : ℕ} (hv : SplitOut D.nd i v)
    (h1 : 1 ≤ k) (h2 : k ≤ D.R.nV) :
    GenAt D (D.what₂.places.resChar (D.nd.w i)) (T.B.Qc (D.nd.j i) (D.nd.w i)) v k := by
  obtain ⟨hs, hl, hS, hQ⟩ := hv
  rw [D.nd.w_l i, ← T.Q_eq _ _ i (mem_locs_self i)]
  exact ⟨hs, hl, fun h => hS ((D.nd.S_def i v).2 h), hQ, h1, h2⟩

theorem splitOut_of_genAt (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    {v : PlE D.host} {k : ℕ} (hg : GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) : SplitOut D.nd i v := by
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  obtain ⟨hs, hl, hS, hQ, -, -⟩ := hg
  have hli : D.what₂.places.resChar w = D.nd.l i := by rw [← e2, D.nd.w_l]
  rw [hli] at hl hS
  refine ⟨hs, hl, fun h' => hS ((D.nd.S_def i v).1 h'), ?_⟩
  rw [T.Q_eq j w i h]; exact hQ

theorem real_transport {w0 : D.what₂.places.Pl} {j0 : ℕ} (b1 : 1 ≤ j0) (b2 : j0 ≤ D.R.m)
    (f : D.what₂.MtL (D.what₂.muTw w0) j0 → D.what₂.MtL (D.what₂.muTw w0) j0) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ)
    (hf : ∀ y, (M (D.what₂.muTw w0) j0 b1 b2).real (D.what₂.jMt _ _ (f y)) =
      NG.tN (M (D.what₂.muTw w0) j0 b1 b2).J s ϖ k ((M (D.what₂.muTw w0) j0 b1 b2).real (D.what₂.jMt _ _ y)))
    (μ : D.what₂.Tup) (jj : ℕ) (e : D.what₂.MtL μ jj = D.what₂.MtL (D.what₂.muTw w0) j0) (hμ : μ = D.what₂.muTw w0)
    (hj : jj = j0) (a1 : 1 ≤ jj) (a2 : jj ≤ D.R.m) (y : D.what₂.MtL μ jj) :
    (M μ jj a1 a2).real (D.what₂.jMt μ jj (cast e.symm (f (cast e y)))) =
      NG.tN (M μ jj a1 a2).J s ϖ k ((M μ jj a1 a2).real (D.what₂.jMt μ jj y)) := by
  subst hμ hj
  simpa only [cast_eq] using hf y

theorem commute_gens (T : NormalizedLocalCompatibility D M) (hstd : HeckeStd T.B) {j : ℕ} (w : D.what₂.places.Pl) (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) :
    ∀ a ∈ heckeGens T.B j w, ∀ b ∈ heckeGens T.B j w, Commute a b := by
  rintro a ⟨v1, k1, hg1, rfl⟩ b ⟨v2, k2, hg2, rfl⟩
  exact (hstd _ _ a1 a2).1 v1 k1 v2 k2 hg1 hg2

theorem hT_of (T : NormalizedLocalCompatibility D M) (hstd : HeckeStd T.B)
    (hact : ∀ j w i (h : i ∈ D.nd.locs j w) v k, GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k → ∀ z,
      T.Psi j w i h (((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) z) =
        T.B.hK j w v k (T.Psi j w i h z)) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hv : SplitOut D.nd i v) (hc : IsConjPl D.host v s.w)
    (hu : IsUnif D.host.E s.v ϖ) (hk1 : 1 ≤ k) (hk2 : k ≤ D.R.nV) (x x' : D.what₂.MtL (D.nd.mu i) (D.nd.j i))
    (hx : (M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x') =
      NG.tN (M.loc i).J s ϖ k ((M.loc i).real (D.what₂.jMt (D.nd.mu i) (D.nd.j i) x))) :
    D.nd.prMt i x' = ((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) (D.nd.prMt i x) := by
  have hi := mem_locs_self (D := D) i
  have hg := genAt_of_splitOut T hv hk1 hk2
  have a1 := (D.nd.j_range i).1
  have a2 := (D.nd.j_range i).2
  have H1 := real_transport (M := M) a1 a2 (T.B.hL (D.nd.j i) (D.nd.w i) v k) s ϖ k
    (T.B.hL_def (D.nd.j i) (D.nd.w i) a1 a2 v k s ϖ hg hc hu) (D.nd.mu i) (D.nd.j i) (mtL_eq D hi) (D.nd.mu_w i) rfl
    a1 a2 x
  have hx' : x' = cast (mtL_eq D hi).symm (T.B.hL (D.nd.j i) (D.nd.w i) v k (cast (mtL_eq D hi) x)) :=
    ((M.loc i).real_inj.comp (jMt_inj' _ _)) (hx.trans H1.symm)
  have hcx : castMt D hi x' = T.B.hL (D.nd.j i) (D.nd.w i) v k (castMt D hi x) := by
    rw [hx']; unfold castMt; exact cast_cast _ _ _
  have hS := commute_gens T hstd (D.nd.w i) a1 a2
  have hinj : Function.Injective (algebraMap (T.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (T.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  apply T.Psi_inj _ _ i hi
  rw [← sub_eq_zero]
  have hpart : T.Psi _ _ i hi (D.nd.prMt i x') -
      T.Psi _ _ i hi (((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) (D.nd.prMt i x)) ∈
      NCov.part (heckeAlg T.B (D.nd.j i) (D.nd.w i)) (T.mx _ _ i) :=
    (T.Psi_range _ _ i hi _).2 ⟨_, map_sub (T.Psi _ _ i hi) _ _⟩
  have hoff : T.Psi _ _ i hi (D.nd.prMt i x') -
      T.Psi _ _ i hi (((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) (D.nd.prMt i x)) ∈
      NCov.off (heckeAlg T.B (D.nd.j i) (D.nd.w i)) (T.mx _ _ i) := by
    rw [hact _ _ i hi v k hg]
    have o1 := T.Psi_pr _ _ i hi x'
    have o2 := off_mapsTo hS (T.mx _ _ i) ⟨T.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hg, rfl⟩⟩ (T.Psi_pr _ _ i hi x)
    have e : T.Psi _ _ i hi (D.nd.prMt i x') - T.B.hK _ _ v k (T.Psi _ _ i hi (D.nd.prMt i x)) =
        (T.Psi _ _ i hi (D.nd.prMt i x') - T.B.iV _ _ (castMt D hi x')) -
          T.B.hK _ _ v k (T.Psi _ _ i hi (D.nd.prMt i x) - T.B.iV _ _ (castMt D hi x)) := by
      rw [map_sub, T.B.hK_def, ← hcx]; abel
    rw [e]; exact Submodule.sub_mem _ o1 o2
  exact (Submodule.disjoint_def.1 (disjoint_part_off hinj hS _)) _ hpart hoff

theorem iotaOC_injective (i : D.nd.Loc) : Function.Injective (iotaOC D i) := by
  intro a b h
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  apply (D.naut.iotaQ i).injective
  apply (D.naut.iotaQC i).injective
  exact h

theorem phO_of_iota (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i i' : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (h' : i' ∈ D.nd.locs j w) (φ : D.nd.O i ≃+* D.nd.O i') (hφ : ∀ z, iotaOC D i z = iotaOC D i' (φ z))
    (z : D.nd.O i) : T.phO j w i' h' (φ z) = T.phO j w i h z := by
  have hinjC : Function.Injective (T.iotaC j w) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := (T.phO j w i h).surjective a
    obtain ⟨b', rfl⟩ := (T.phO j w i h).surjective b
    rw [← T.iotaC_coh, ← T.iotaC_coh] at hab
    rw [iotaOC_injective i hab]
  apply hinjC
  rw [← T.iotaC_coh, ← T.iotaC_coh]
  exact (hφ z).symm

theorem sameO_of (T : NormalizedLocalCompatibility D M) (i i' : D.nd.Loc) (hj : D.nd.j i = D.nd.j i') (hw : D.nd.w i = D.nd.w i') :
    ∃ φ : D.nd.O i ≃+* D.nd.O i', ∀ z, iotaOC D i z = iotaOC D i' (φ z) := by
  have hi := mem_locs_self (D := D) i
  have hi' : i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i').2 ⟨hj.symm, hw.symm⟩
  refine ⟨(T.phO _ _ i hi).trans (T.phO _ _ i' hi').symm, fun z => ?_⟩
  rw [T.iotaC_coh _ _ i hi, T.iotaC_coh _ _ i' hi', RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

theorem sep_of (T : NormalizedLocalCompatibility D M) (hstd : HeckeStd T.B) (i i' : D.nd.Loc) (φ : D.nd.O i ≃+* D.nd.O i')
    (hφ : ∀ z, iotaOC D i z = iotaOC D i' (φ z)) (hj : D.nd.j i = D.nd.j i') (hw : D.nd.w i = D.nd.w i')
    (hne : i ≠ i') (x : D.nd.X i) (x' : D.nd.X i') :
    ∃ (v : PlE D.host) (k : ℕ), SplitOut D.nd i v ∧ SplitOut D.nd i' v ∧ 1 ≤ k ∧ k ≤ D.R.nV ∧
      IsUnit (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x') := by
  have hi := mem_locs_self (D := D) i
  have hi' : i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i').2 ⟨hj.symm, hw.symm⟩
  have hS := commute_gens T hstd (D.nd.w i) (D.nd.j_range i).1 (D.nd.j_range i).2
  have hcls : NCov.cls (T.ptX _ _ i hi x).1 ≠ NCov.cls (T.ptX _ _ i' hi' x').1 := by
    rw [(T.ptX _ _ i hi x).2.1, (T.ptX _ _ i' hi' x').2.1]
    exact fun e => hne (T.mx_inj _ _ hi hi' e)
  obtain ⟨s, ⟨v, k, hg, rfl⟩, hu⟩ := exists_unit_of_cls_ne _ _ hcls
  have e1 := T.ptX_hT _ _ i hi x v k hg
  have e2 := T.ptX_hT _ _ i' hi' x' v k hg
  refine ⟨v, k, splitOut_of_genAt T hi hg, splitOut_of_genAt T hi' hg, hg.2.2.2.2.1, hg.2.2.2.2.2, ?_⟩
  rw [← e1, ← e2, ← phO_of_iota T hi hi' φ hφ, ← map_sub] at hu
  exact (isUnit_map_iff (T.phO _ _ i' hi') _).1 hu

theorem Q_conj_of (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (w w' : PlE D.host) (hc : IsConjPl D.host w w')
    (hw : w ∈ D.nd.Q i) : w' ∈ D.nd.Q i := by
  have hi := mem_locs_self (D := D) i
  rw [T.Q_eq _ _ i hi] at hw ⊢
  exact T.B.Qc_conj _ _ w' w hw (isConjPl_symm' hc)

theorem Q_same_of (T : NormalizedLocalCompatibility D M) (hQc : ∀ j j' w, T.B.Qc j w = T.B.Qc j' w) (i i' : D.nd.Loc)
    (hw : D.nd.w i = D.nd.w i') : D.nd.Q i = D.nd.Q i' := by
  rw [T.Q_eq _ _ i (mem_locs_self i), T.Q_eq _ _ i' (mem_locs_self i'), hw, hQc]

theorem rational_of (T : NormalizedLocalCompatibility D M) : HeckeRational D M := by
  intro i v k s ϖ hv hc hu hk1 hk2 x
  have hi := mem_locs_self (D := D) i
  have hg := genAt_of_splitOut T hv hk1 hk2
  have a1 := (D.nd.j_range i).1
  have a2 := (D.nd.j_range i).2
  exact ⟨_, real_transport (M := M) a1 a2 (T.B.hL (D.nd.j i) (D.nd.w i) v k) s ϖ k
    (T.B.hL_def (D.nd.j i) (D.nd.w i) a1 a2 v k s ϖ hg hc hu) (D.nd.mu i) (D.nd.j i) (mtL_eq D hi) (D.nd.mu_w i) rfl
    a1 a2 x⟩

theorem hypOutside_mono (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
    {B B' : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))} (hB : B ⊆ B') (h : NG.HypOutside J χ B) :
    NG.HypOutside J χ B' := by
  intro κ hκ
  apply h κ
  intro v hv
  apply hκ v
  rw [Set.mem_compl_iff, not_not]
  rw [Set.mem_compl_iff, not_not] at hv
  exact hB hv

theorem gPl_sub_badPl (i : D.nd.Loc) : gPl D ⊆ badPl D i := by
  rintro v ⟨w, hw, k, hk⟩
  exact ⟨w, hw, Or.inr (Or.inl ⟨k, hk⟩)⟩

theorem mt_transport (M : MtFam D) (P : ∀ (μ : D.what₂.Tup) (j : ℕ), MtReal D μ j → Prop) {μ μ' : D.what₂.Tup} {j j' : ℕ}
    (hμ : μ = μ') (hj : j = j') (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) :
    P μ j (M μ j a1 a2) → P μ' j' (M μ' j' b1 b2) := by
  subst hμ hj; exact id

end Gen

section Chars
open Formalism.L2.Host

theorem infG_etaT {D : D7} {cf : CharFrame D} (chr : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := by
  have h : (chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => 1 / 2) := by
    rw [chr.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  exact (chr.infG _ _ h (D.eTau t)).1

theorem qPl_sub {D : D7} {cf : CharFrame D} {C : NChoice D} (tp : TupTied D cf C) (w : D.what₂.places.Pl)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (j : Fin D.R.m) :
    qPl D (tp.tup (D.what₂.muTw w) j) ⊆ {v | ∃ w' : PlE D.host, NG.OverPl w' v ∧ (w' ∈ C.Q w ∨
      w' ∈ placesOver D.host.E (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde))} := by
  rintro v ⟨hg, w', hov, hu⟩
  refine ⟨w', hov, ?_⟩
  by_contra hno
  simp only [not_or] at hno
  apply hu
  unfold TupTied.tup
  rw [tp.xi_tw]
  refine HChar.UnrAt.mul ((cf.isMu0 j).unr w' fun k hk => hg ⟨w', hov, k, hk⟩) (HChar.UnrAt.mul ?_ ?_)
  · unfold CharFrame.delAt
    split_ifs with h
    · exact cf.isDel'.unr w' fun hp => hno.2 (by rw [if_pos h]; exact hp)
    · exact cf.isDel.unr w' fun hp => hno.2 (by rw [if_neg h]; exact hp)
  · exact ((tp.psi_is w hw).ram w').2 hno.1

end Chars

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem heckeOpen_withLoc : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : AutSpec A M tp.tup Sp.iq L.Y L.C), ∃ Hk : HeckeOpen (withLoc L) (mtL L M) tp.tup, ∀ j h1 h2 π, Hk.au.cls j h1 h2 π = A.au.cls j h1 h2 π := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hjf : ∀ i : L.X.Loc, L.X.j i - 1 + 1 = L.X.j i := fun i => by have := L.X.j_range i; omega
  let jf : L.X.Loc → Fin D.R.m := fun i => ⟨L.X.j i - 1, by have := L.X.j_range i; omega⟩
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStd cover.B := Sp.std
  refine ⟨{ hecke := ?_, av := { S := Au.S, irr := Au.irr, inj := Au.inj, surj := Au.surj, typeV := Au.typeV, ptV := Au.ptV }, au := { A.au with }, emb := Au.emb, rational := rational_of cover, level := ?_, data := { bj := Sp.bj, bj_span := Sp.bj_span, bj_rel := fun i c => Sp.bj_rel i (sOf _ i) (sOf_spec _ i) c }, cover := cover }, fun j h1 h2 π => rfl⟩
  · refine { J_hyp := fun i => ?_
             hT := hT_of cover hstd Sp.act_hK
             sameO := sameO_of cover
             sep := sep_of cover hstd
             Q_conj := Q_conj_of cover
             Q_same := Q_same_of cover fun j j' w => (Sp.Qc_eq j w).trans (Sp.Qc_eq j' w).symm }
    have h0 := hMt.hyp (L.X.w i) (jf i)
    have h1 := hypOutside_transport' (M := M) (L.X.mu_w i).symm (hjf i) _ _ (L.X.j_range i).1 (L.X.j_range i).2 _ h0
    refine hypOutside_mono (D := withLoc L) _ _ ?_ h1
    have hi := mem_locs_self (D := withLoc L) i
    have hQe : C.Q (L.X.w i) = L.X.Q i := ((Sp.Q_eq _ _ i hi).trans (Sp.Qc_eq _ _)).symm
    intro v hv
    rcases hv with hv | hv
    · exact gPl_sub_badPl (D := withLoc L) i hv
    · obtain ⟨w', hov, hw'⟩ := qPl_sub tp (L.X.w i) (L.X.w_tw i) (jf i) hv
      refine ⟨w', hov, ?_⟩
      rcases hw' with hQ | hp
      · left
        rw [hQe] at hQ
        exact hQ
      · right; right
        rw [L.X.w_l i] at hp
        exact hp
  · refine { prod := ?_, para := ?_, uni := ?_, wt := ?_, hyp := ?_ }
    · exact fun i => mt_transport M (fun μ j m => NG.IsProdLevel m.J) (L.X.mu_w i).symm (hjf i) _ _ _ _
        (hMt.prod (L.X.w i) (jf i))
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ v ∈ qPl D (tp.tup μ j),
        ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.para (L.X.w i) j)
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
        s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.uni (L.X.w i) j)
    · intro μ j t sh a lam hinf hdual hhw
      have e := infG_etaT A.chr t
      have hsh : sh = 1 / 2 := by
        have := Multiset.singleton_inj.1 (hinf.symm.trans e)
        rw [this]; push_cast; ring
      rw [hsh]
      exact hMt.wt μ j t a lam hdual hhw
    · exact fun i j hj => mt_transport M (fun μ jj m => NG.HypOutside m.J m.χ (gPl D ∪ qPl D (tp.tup μ j)))
        (L.X.mu_w i).symm hj _ _ _ _ (hMt.hyp (L.X.w i) j)

end GlobalTheory.FitHecke
