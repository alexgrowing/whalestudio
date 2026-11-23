import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverLen

noncomputable section

open Formalism.BasicNotions Module Module.End

namespace Formalism.L2.NCov

section Eig

variable {O K V : Type} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

def E (T : Subalgebra O (End K V)) (ψ : T →ₐ[O] O) : Submodule K V :=
  ⨅ t : T, (t : End K V).eigenspace (pt ψ t)

def eSum (T : Subalgebra O (End K V)) (Y : Set (T →ₐ[O] O)) : Submodule K V :=
  ⨆ ψ ∈ Y, E T ψ

theorem E_le_W_pt (T : Subalgebra O (End K V)) (ψ : T →ₐ[O] O) : E T ψ ≤ W T (pt ψ) :=
  iInf_mono fun _ => eigenspace_le_maxGenEigenspace

theorem mem_E_iff {S : Set (End K V)} (ψ : Algebra.adjoin O S →ₐ[O] O) (z : V) :
    z ∈ E (Algebra.adjoin O S) ψ ↔
      ∀ s (hs : s ∈ S), s z = pt ψ ⟨s, Algebra.subset_adjoin hs⟩ • z := by
  constructor
  · intro hz s hs
    have := (Submodule.mem_iInf _).1 hz ⟨s, Algebra.subset_adjoin hs⟩
    exact mem_eigenspace_iff.1 this
  · intro hz
    refine (Submodule.mem_iInf _).2 fun t => ?_
    rw [mem_eigenspace_iff]
    obtain ⟨t, ht⟩ := t
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hz x hx
    | algebraMap r =>
      change (algebraMap O (End K V) r) z = pt ψ (algebraMap O (Algebra.adjoin O S) r) • z
      simp [pt, algebraMap_smul, Module.algebraMap_end_apply]
    | add x y hx hy ihx ihy =>
      change (x + y) z = pt ψ (⟨x, hx⟩ + ⟨y, hy⟩) • z
      simp only [pt, map_add, LinearMap.add_apply, add_smul] at ihx ihy ⊢
      rw [ihx, ihy]
    | mul x y hx hy ihx ihy =>
      change (x * y) z = pt ψ (⟨x, hx⟩ * ⟨y, hy⟩) • z
      simp only [pt, map_mul, Module.End.mul_apply] at ihx ihy ⊢
      rw [ihy, LinearMap.map_smul, ihx, smul_smul, mul_comm]

variable [IsLocalRing O]

theorem W_le_part (T : Subalgebra O (End K V)) (ψ : T →ₐ[O] O) : W T (pt ψ) ≤ part T (cls ψ) :=
  le_iSup₂_of_le (f := fun (ψ' : T →ₐ[O] O) (_ : cls ψ' = cls ψ) => W T (pt ψ')) ψ rfl le_rfl

theorem E_le_part (T : Subalgebra O (End K V)) (ψ : T →ₐ[O] O) : E T ψ ≤ part T (cls ψ) :=
  (E_le_W_pt T ψ).trans (W_le_part T ψ)

theorem disjoint_part_off [FiniteDimensional K V] {S : Set (End K V)}
    (hinj : Function.Injective (algebraMap O K)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (𝔪 : Ideal (Algebra.adjoin O S)) :
    Disjoint (part (Algebra.adjoin O S) 𝔪) (off (Algebra.adjoin O S) 𝔪) := by
  classical
  have hind : iSupIndep (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) :=
    (iSupIndep_alt hS).comp (pt_injective hinj)
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hind
  have hF : ∀ ψ, W _ (pt ψ) ≠ ⊥ → ψ ∈ hfin.toFinset := fun ψ h => hfin.mem_toFinset.2 h
  have h1 : part (Algebra.adjoin O S) 𝔪 =
      (hfin.toFinset.filter (fun ψ => cls ψ = 𝔪)).sup (fun ψ => W _ (pt ψ)) :=
    iSup_eq_sup_filter (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) _ hF _
  have h2 : off (Algebra.adjoin O S) 𝔪 =
      (hfin.toFinset.filter (fun ψ => cls ψ ≠ 𝔪)).sup (fun ψ => W _ (pt ψ)) :=
    iSup_eq_sup_filter (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) _ hF _
  rw [h1, h2]
  exact (hind.supIndep' _).disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (Finset.disjoint_filter.2 fun ψ _ h h' => h' h)

def latPart (T : Subalgebra O (End K V)) (Λ : Submodule O V) (𝔪 : Ideal T) : Submodule O V :=
  (part T 𝔪).restrictScalars O ⊓ (Λ ⊔ (off T 𝔪).restrictScalars O)

def etaAt (T : Subalgebra O (End K V)) (Λ : Submodule O V) (G : Set (T →ₐ[O] O)) (l : ℕ) (𝔪 : Ideal T) : ℚ :=
  let L := latPart T Λ 𝔪
  let good := (eSum T {ψ | ψ ∈ G ∧ cls ψ = 𝔪}).restrictScalars O
  let bad := (eSum T {ψ | ψ ∉ G ∧ cls ψ = 𝔪}).restrictScalars O
  let up := good ⊓ (L ⊔ bad)
  let low := L ⊓ good
  lenUnit (O := O) l (↥up ⧸ low.comap up.subtype)

end Eig

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def latC (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Submodule (B.Oc j w) (B.V j w) :=
  Submodule.span (B.Oc j w)
    (B.iV j w '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen})

def etaC (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (G : Set (heckeAlg B j w →ₐ[B.Oc j w] B.Oc j w)) : ℚ :=
  ∑ᶠ 𝔪 ∈ {𝔪 : Ideal (heckeAlg B j w) | 𝔪.IsMaximal},
    NCov.etaAt (heckeAlg B j w) (latC B j w) G (D.what₂.places.resChar w) 𝔪

end Formalism.L2

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def PsiAct (T : NormalizedLocalCompatibility D M) : Prop :=
  ∀ j w i (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ),
    GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k →
    ∀ z, T.Psi j w i h (((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) z) =
      T.B.hK j w v k (T.Psi j w i h z)

theorem genAt_iff (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (v : PlE D.host) (k : ℕ) :
    (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k := by
  obtain ⟨-, h2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, h2]
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar w) := by
    rw [D.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, T.Q_eq j w i h, hl]
  tauto

theorem mem_heckeEig_iff (i : D.nd.Loc) (x : D.nd.X i)
    (y : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :
    y ∈ heckeEig (D.nd.T i) (D.nd.act i) x ↔ ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV →
      ((D.nd.act i (D.nd.hT i v k)).baseChange (FractionRing (D.nd.O i))) y =
        algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) • y := by
  constructor
  · intro hy v k _ _ _
    exact mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy (D.nd.hT i v k))
  · intro hy
    refine (Submodule.mem_iInf _).2 fun f => mem_eigenspace_iff.2 ?_
    obtain ⟨f, hf⟩ := f
    have hf' := hf
    rw [← D.nd.T_gen i] at hf'
    suffices key : ∀ g (hg' : g ∈ Algebra.adjoin (D.nd.O i) {g : D.nd.X i → D.nd.O i | ∃ v k, IsSplitPl D.host v ∧
        v ∉ placesOver D.host.E (D.nd.l i) ∧ v ∉ D.nd.S i ∧ v ∉ D.nd.Q i ∧ 1 ≤ k ∧ k ≤ D.R.nV ∧
        g = (D.nd.hT i v k : D.nd.X i → D.nd.O i)}), ∀ hg : g ∈ D.nd.T i,
        ((D.nd.act i ⟨g, hg⟩).baseChange (FractionRing (D.nd.O i))) y =
          algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (g x) • y from key f hf' hf
    intro g hg'
    induction hg' using Algebra.adjoin_induction with
    | mem g hg0 =>
      intro hg
      obtain ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩ := hg0
      exact hy v k ⟨h1, h2, h3, h4⟩ h5 h6
    | algebraMap r =>
      intro hg
      have e : (⟨algebraMap (D.nd.O i) (D.nd.X i → D.nd.O i) r, hg⟩ : D.nd.T i) =
          algebraMap (D.nd.O i) (D.nd.T i) r := rfl
      rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
        LinearMap.baseChange_one]
      simp [algebraMap_smul]
    | add g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ D.nd.T i := D.nd.T_gen i ▸ hg1
      have m2 : g' ∈ D.nd.T i := D.nd.T_gen i ▸ hg2
      have e : (⟨g + g', hg⟩ : D.nd.T i) = ⟨g, m1⟩ + ⟨g', m2⟩ := rfl
      rw [e, map_add, LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2, Pi.add_apply, map_add,
        add_smul]
    | mul g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ D.nd.T i := D.nd.T_gen i ▸ hg1
      have m2 : g' ∈ D.nd.T i := D.nd.T_gen i ▸ hg2
      have e : (⟨g * g', hg⟩ : D.nd.T i) = ⟨g, m1⟩ * ⟨g', m2⟩ := rfl
      rw [e, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1,
        smul_smul, Pi.mul_apply, map_mul, mul_comm]

theorem psi_mem_E_iff (T : NormalizedLocalCompatibility D M) (hact : PsiAct T) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) (x : D.nd.X i) (y : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :
    y ∈ heckeEig (D.nd.T i) (D.nd.act i) x ↔
      T.Psi j w i h y ∈ NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
  have hval : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k),
      (T.phK j w i h).toRingHom
          (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) =
        NCov.pt (T.ptX j w i h x).1 ⟨T.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
    intro v k hvk
    exact (T.phK_alg j w i h _).trans (congrArg _ (T.ptX_hT j w i h x v k hvk))
  rw [mem_heckeEig_iff, NCov.mem_E_iff]
  constructor
  · rintro hy _ ⟨v, k, hvk, rfl⟩
    obtain ⟨hso, hk1, hk2⟩ := (genAt_iff T h v k).2 hvk
    have e := congrArg (T.Psi j w i h) (hy v k hso hk1 hk2)
    rw [hact j w i h v k hvk, LinearMap.map_smulₛₗ, hval v k hvk] at e
    exact e
  · intro hy v k hso hk1 hk2
    have hvk := (genAt_iff T h v k).1 ⟨hso, hk1, hk2⟩
    apply T.Psi_inj j w i h
    rw [hact j w i h v k hvk, LinearMap.map_smulₛₗ, hval v k hvk]
    exact hy _ ⟨v, k, hvk, rfl⟩

end Formalism.L2

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

theorem jMt_cast_mem {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (e : D.what₂.MtL μ j = D.what₂.MtL μ' j') (x : D.what₂.MtL μ j) :
    D.what₂.jMt μ' j' (cast e x) ∈ (D.what₂.MtLat μ' j').gen ↔ D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen := by
  subst hμ; subst hj; rfl

theorem castMt_mem {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) :
    D.what₂.jMt (D.what₂.muTw w) j (castMt D h x) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen ↔
      D.what₂.jMt (D.nd.mu i) (D.nd.j i) x ∈ (D.what₂.MtLat (D.nd.mu i) (D.nd.j i)).gen :=
  jMt_cast_mem (by rw [D.nd.mu_w i, ((D.nd.locs_mem j w i).1 h).2]) ((D.nd.locs_mem j w i).1 h).1 _ x

theorem castMtInv_mem {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) :
    D.what₂.jMt (D.nd.mu i) (D.nd.j i) (castMtInv D h y) ∈ (D.what₂.MtLat (D.nd.mu i) (D.nd.j i)).gen ↔
      D.what₂.jMt (D.what₂.muTw w) j y ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen := by
  rw [← castMt_mem h, castMt_castMtInv]

def psiO (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) →ₛₗ[(T.phO j w i h : D.nd.O i →+* T.B.Oc j w)]
      T.B.V j w where
  toFun := T.Psi j w i h
  map_add' := map_add _
  map_smul' c z := by
    rw [← algebraMap_smul (FractionRing (D.nd.O i)) c z, LinearMap.map_smulₛₗ]
    change (T.phK j w i h) (algebraMap _ _ c) • _ = _
    rw [T.phK_alg, algebraMap_smul]
    rfl

theorem psiO_apply (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) (z) :
    psiO T h z = T.Psi j w i h z := rfl

theorem psiO_injective (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) : Function.Injective (psiO T h) := T.Psi_inj j w i h

theorem map_psiO_rs (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (p : Submodule (FractionRing (D.nd.O i)) (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)))
    (q : Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w))
    (hpq : ∀ y, y ∈ p ↔ T.Psi j w i h y ∈ q) (hq : ∀ z ∈ q, ∃ y, T.Psi j w i h y = z) :
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
    (p.restrictScalars (D.nd.O i)).map (psiO T h) = q.restrictScalars (T.B.Oc j w) := by
  haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
  ext z
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem, psiO_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hpq y).1 hy
  · intro hz
    obtain ⟨y, rfl⟩ := hq z hz
    exact ⟨y, (hpq y).2 hz, rfl⟩

theorem psi_mem_sum_iff (T : NormalizedLocalCompatibility D M) (hact : PsiAct T) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) (Y : Set (D.nd.X i))
    (y : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :
    y ∈ D.nd.eigSum i Y ↔
      T.Psi j w i h y ∈ ⨆ x ∈ Y, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
  haveI : RingHomSurjective (T.phK j w i h).toRingHom := ⟨(T.phK j w i h).surjective⟩
  have hx : ∀ x, (heckeEig (D.nd.T i) (D.nd.act i) x).map (T.Psi j w i h) =
      NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
    intro x
    ext z
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (psi_mem_E_iff T hact h x y).1 hy
    · intro hz
      have hz' : z ∈ NCov.part (heckeAlg T.B j w) (T.mx j w i) := by
        have := NCov.E_le_part (heckeAlg T.B j w) (T.ptX j w i h x).1 hz
        rwa [(T.ptX j w i h x).2.1] at this
      obtain ⟨y, rfl⟩ := (T.Psi_range j w i h z).1 hz'
      exact ⟨y, (psi_mem_E_iff T hact h x y).2 hz, rfl⟩
  have hmap : (D.nd.eigSum i Y).map (T.Psi j w i h) =
      ⨆ x ∈ Y, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
    unfold NData.eigSum
    rw [Submodule.map_iSup]
    refine iSup_congr fun x => ?_
    rw [Submodule.map_iSup]
    exact iSup_congr fun _ => hx x
  rw [← hmap]
  constructor
  · intro hy; exact Submodule.mem_map_of_mem hy
  · rintro ⟨y', hy', e⟩
    rwa [← T.Psi_inj j w i h e]

theorem sum_E_le_part (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) (Y : Set (D.nd.X i)) :
    (⨆ x ∈ Y, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1) ≤ NCov.part (heckeAlg T.B j w) (T.mx j w i) :=
  iSup₂_le fun x _ => by
    have := NCov.E_le_part (heckeAlg T.B j w) (T.ptX j w i h x).1
    rwa [(T.ptX j w i h x).2.1] at this

theorem eSum_eq (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (G : Set (heckeAlg T.B j w →ₐ[T.B.Oc j w] T.B.Oc j w)) :
    NCov.eSum (heckeAlg T.B j w) {ψ | ψ ∈ G ∧ NCov.cls ψ = T.mx j w i} =
      ⨆ x ∈ {x | (T.ptX j w i h x).1 ∈ G}, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
  apply le_antisymm
  · refine iSup₂_le fun ψ hψ => ?_
    by_cases hE : NCov.E (heckeAlg T.B j w) ψ = ⊥
    · rw [hE]; exact bot_le
    · have hW : NCov.W (heckeAlg T.B j w) (NCov.pt ψ) ≠ ⊥ := fun h0 =>
        hE (eq_bot_iff.2 ((NCov.E_le_W_pt _ ψ).trans h0.le))
      set x := (T.ptX j w i h).symm ⟨ψ, hψ.2, hW⟩
      have hxψ : (T.ptX j w i h x).1 = ψ := by simp [x]
      refine le_iSup₂_of_le (f := fun x (_ : x ∈ {x | (T.ptX j w i h x).1 ∈ G}) =>
        NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1) x (by simp only [Set.mem_ofPred_eq, hxψ]; exact hψ.1) ?_
      rw [hxψ]
  · refine iSup₂_le fun x hx => ?_
    exact le_iSup₂_of_le (f := fun ψ (_ : ψ ∈ {ψ | ψ ∈ G ∧ NCov.cls ψ = T.mx j w i}) =>
      NCov.E (heckeAlg T.B j w) ψ) (T.ptX j w i h x).1 ⟨hx, (T.ptX j w i h x).2.1⟩ le_rfl

end Formalism.L2

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

theorem map_psiO_MtIn (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) :
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
    (D.nd.MtIn i).map (psiO T h) = NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) := by
  haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
  obtain ⟨e1, -⟩ := (D.nd.locs_mem j w i).1 h
  have h1 : 1 ≤ j := e1 ▸ (D.nd.j_range i).1
  have h2 : j ≤ D.R.m := e1 ▸ (D.nd.j_range i).2
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, -, -⟩ := gens_hypsTw T.B hstd h1 h2 (locPl_of_mem D h)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  have hdisj := NCov.disjoint_part_off hinj hS (T.mx j w i)
  set gi := {x | D.what₂.jMt (D.nd.mu i) (D.nd.j i) x ∈ (D.what₂.MtLat (D.nd.mu i) (D.nd.j i)).gen}
  have hIn : D.nd.MtIn i = Submodule.span (D.nd.O i) (D.nd.prMt i '' gi) := (D.nd.prMt_lat i).symm
  rw [hIn, Submodule.map_span]
  set L' := Submodule.span (T.B.Oc j w) (psiO T h '' (D.nd.prMt i '' gi))
  set P := (NCov.part (heckeAlg T.B j w) (T.mx j w i)).restrictScalars (T.B.Oc j w)
  set Q := (NCov.off (heckeAlg T.B j w) (T.mx j w i)).restrictScalars (T.B.Oc j w)
  have hL'P : L' ≤ P := Submodule.span_le.2 <| by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact (T.Psi_range j w i h _).2 ⟨_, rfl⟩
  have hL'lat : L' ≤ latC T.B j w ⊔ Q := Submodule.span_le.2 <| by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have e : psiO T h (D.nd.prMt i x) = T.B.iV j w (castMt D h x) +
        (T.Psi j w i h (D.nd.prMt i x) - T.B.iV j w (castMt D h x)) := by
      rw [psiO_apply]; abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨castMt D h x, (castMt_mem h x).2 hx, rfl⟩) ?_
    exact T.Psi_pr j w i h x
  have hlat : latC T.B j w ≤ L' ⊔ Q := Submodule.span_le.2 <| by
    rintro _ ⟨y, hy, rfl⟩
    have e : T.B.iV j w y = psiO T h (D.nd.prMt i (castMtInv D h y)) -
        (T.Psi j w i h (D.nd.prMt i (castMtInv D h y)) - T.B.iV j w (castMt D h (castMtInv D h y))) := by
      rw [castMt_castMtInv, psiO_apply]; abel
    rw [e]
    refine Submodule.sub_mem_sup (Submodule.subset_span ⟨_, ⟨castMtInv D h y, (castMtInv_mem h y).2 hy, rfl⟩, rfl⟩) ?_
    exact T.Psi_pr j w i h _
  have hPQ : Q ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (Submodule.mem_bot _).2 (Submodule.disjoint_def.1 hdisj z hz.2 hz.1)
  apply le_antisymm
  · exact le_inf hL'P hL'lat
  · calc NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) = P ⊓ (latC T.B j w ⊔ Q) := rfl
      _ ≤ P ⊓ (L' ⊔ Q) := inf_le_inf_left _ (sup_le hlat le_sup_right)
      _ = L' ⊔ Q ⊓ P := by rw [inf_comm, sup_inf_assoc_of_le Q hL'P]
      _ = L' := by rw [hPQ, sup_bot_eq]

theorem etaLoc_eq_etaAt (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (hact : PsiAct T)
    {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (G : Set (heckeAlg T.B j w →ₐ[T.B.Oc j w] T.B.Oc j w))
    (hG : ∀ x, x ∈ D.nd.Zgood i ↔ (T.ptX j w i h x).1 ∈ G) :
    D.nd.etaLoc i = NCov.etaAt (heckeAlg T.B j w) (latC T.B j w) G (D.what₂.places.resChar w) (T.mx j w i) := by
  haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hY1 : {x | (T.ptX j w i h x).1 ∈ G} = (↑(D.nd.Zgood i) : Set (D.nd.X i)) := by
    ext x; exact (hG x).symm
  have hY2 : {x | (T.ptX j w i h x).1 ∈ Gᶜ} = (↑(D.nd.Zgood i) : Set (D.nd.X i))ᶜ := by
    ext x; simp only [Set.mem_compl_iff]; exact not_congr (hG x).symm
  have hgood : NCov.eSum (heckeAlg T.B j w) {ψ | ψ ∈ G ∧ NCov.cls ψ = T.mx j w i} =
      ⨆ x ∈ (↑(D.nd.Zgood i) : Set (D.nd.X i)), NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
    rw [eSum_eq T h G, hY1]
  have hbad : NCov.eSum (heckeAlg T.B j w) {ψ | ψ ∉ G ∧ NCov.cls ψ = T.mx j w i} =
      ⨆ x ∈ (↑(D.nd.Zgood i) : Set (D.nd.X i))ᶜ, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1 := by
    rw [← hY2]; exact eSum_eq T h Gᶜ
  have hq : ∀ (Y : Set (D.nd.X i)) z, z ∈ (⨆ x ∈ Y, NCov.E (heckeAlg T.B j w) (T.ptX j w i h x).1) →
      ∃ y, T.Psi j w i h y = z := fun Y z hz =>
    (T.Psi_range j w i h z).1 (sum_E_le_part T h Y hz)
  have mgood := map_psiO_rs T h (D.nd.eigSum i ↑(D.nd.Zgood i)) _
    (psi_mem_sum_iff T hact h _) (hq _)
  have mbad := map_psiO_rs T h (D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ) _
    (psi_mem_sum_iff T hact h _) (hq _)
  have mlat := map_psiO_MtIn T hstd h
  unfold NData.etaLoc NData.MtUp NData.MtLow NCov.etaAt
  simp only []
  rw [hgood, hbad, ← mgood, ← mbad, ← mlat, ← Submodule.map_sup, ← Submodule.map_inf _ (psiO_injective T h),
    ← Submodule.map_inf _ (psiO_injective T h)]
  unfold lenUnit
  rw [NCov.length_quot_map (T.phO j w i h) (psiO T h) (psiO_injective T h),
    NCov.length_quot_natCast (T.phO j w i h), hl]

theorem etaC_eq_sum (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (hact : PsiAct T)
    {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (G : Set (heckeAlg T.B j w →ₐ[T.B.Oc j w] T.B.Oc j w))
    (hG : ∀ i (h : i ∈ D.nd.locs j w) x, x ∈ D.nd.Zgood i ↔ (T.ptX j w i h x).1 ∈ G) :
    etaC T.B j w G = ∑ i ∈ D.nd.locs j w, D.nd.etaLoc i := by
  classical
  have hset : {𝔪 : Ideal (heckeAlg T.B j w) | 𝔪.IsMaximal} = ↑((D.nd.locs j w).image (T.mx j w)) := by
    ext 𝔪
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · intro hm
      obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw 𝔪 hm
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact T.mx_max j w i hi
  unfold etaC
  rw [hset, finsum_mem_coe_finset, Finset.sum_image fun a ha b hb hab => T.mx_inj j w ha hb hab]
  exact Finset.sum_congr rfl fun i hi => (etaLoc_eq_etaAt T hstd hact hi G (hG i hi)).symm

theorem etaC_eq_etaJ (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (hact : PsiAct T)
    {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (G : Set (heckeAlg T.B j w →ₐ[T.B.Oc j w] T.B.Oc j w))
    (hG : ∀ i (h : i ∈ D.nd.locs j w) x, x ∈ D.nd.Zgood i ↔ (T.ptX j w i h x).1 ∈ G) :
    etaC T.B j w G = D.what₂.etaJ j w := by
  rw [etaC_eq_sum T hstd hact h1 h2 hw G hG]
  exact (D.etaJ_tie j w h1 h2).symm

end Formalism.L2

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def goodPts (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Set (heckeAlg T.B j w →ₐ[T.B.Oc j w] T.B.Oc j w) :=
  {ψ | ∃ i, ∃ h : i ∈ D.nd.locs j w, ∃ x ∈ D.nd.Zgood i, (T.ptX j w i h x).1 = ψ}

theorem mem_goodPts_iff (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc}
    (h : i ∈ D.nd.locs j w) (x : D.nd.X i) :
    x ∈ D.nd.Zgood i ↔ (T.ptX j w i h x).1 ∈ goodPts T j w := by
  constructor
  · intro hx
    exact ⟨i, h, x, hx, rfl⟩
  · rintro ⟨i', h', x', hx', e⟩
    have hc : T.mx j w i' = T.mx j w i := by
      rw [← (T.ptX j w i' h' x').2.1, ← (T.ptX j w i h x).2.1, e]
    have hi : i' = i := T.mx_inj j w h' h hc
    subst hi
    have : x' = x := (T.ptX j w i' h).injective (Subtype.ext e)
    rwa [← this]

theorem etaC_goodPts_eq_etaJ (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) (hact : PsiAct T)
    {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaC T.B j w (goodPts T j w) = D.what₂.etaJ j w :=
  etaC_eq_etaJ T hstd hact h1 h2 hw _ fun _ h x => mem_goodPts_iff T h x

end Formalism.L2

namespace Formalism.L2.NCov

variable {O K V : Type} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]

theorem lenUnit_subsingleton (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] (hM : Subsingleton M) :
    Formalism.BasicNotions.lenUnit (O := O) l M = 0 := by
  unfold Formalism.BasicNotions.lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaAt_noGood (T : Subalgebra O (End K V)) (Λ : Submodule O V) (G : Set (T →ₐ[O] O)) (l : ℕ)
    (𝔪 : Ideal T) (h : ∀ ψ ∈ G, cls ψ ≠ 𝔪) : etaAt T Λ G l 𝔪 = 0 := by
  have he : {ψ | ψ ∈ G ∧ cls ψ = 𝔪} = (∅ : Set (T →ₐ[O] O)) := by
    ext ψ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]; exact h ψ
  have h0 : eSum T (∅ : Set (T →ₐ[O] O)) = ⊥ := by simp [eSum]
  unfold etaAt
  dsimp only
  rw [he, h0, Submodule.restrictScalars_bot, bot_inf_eq]
  exact lenUnit_subsingleton l _ inferInstance

theorem etaAt_allGood (T : Subalgebra O (End K V)) (Λ : Submodule O V) (G : Set (T →ₐ[O] O)) (l : ℕ)
    (𝔪 : Ideal T) (h : ∀ ψ, cls ψ = 𝔪 → ψ ∈ G) : etaAt T Λ G l 𝔪 = 0 := by
  have he : {ψ | ψ ∉ G ∧ cls ψ = 𝔪} = (∅ : Set (T →ₐ[O] O)) := by
    ext ψ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hn hc; exact hn (h ψ hc)
  have h0 : eSum T (∅ : Set (T →ₐ[O] O)) = ⊥ := by simp [eSum]
  unfold etaAt
  dsimp only
  rw [he, h0, Submodule.restrictScalars_bot, sup_bot_eq]
  apply lenUnit_subsingleton
  refine Submodule.Quotient.subsingleton_iff.2 ?_
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf] at hx ⊢
  exact ⟨hx.2, hx.1⟩

variable {S : Set (End K V)}

theorem finite_maximal [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) :
    {𝔪 : Ideal (Algebra.adjoin O S) | 𝔪.IsMaximal}.Finite := by
  classical
  obtain ⟨F, hF, -⟩ := exists_finset_pts hinj hS hsplit hint
  refine (F.finite_toSet.image cls).subset ?_
  intro 𝔪 h𝔪
  obtain ⟨ψ, hW, rfl⟩ := exists_pt_of_isMaximal hinj hS hsplit hint 𝔪 h𝔪
  exact ⟨ψ, hF ψ hW, rfl⟩

end Formalism.L2.NCov
