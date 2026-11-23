import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetChangeOfBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem spec_dual_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem tan_of_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} {e : Li}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  unfold IsTanAt at hv ⊢
  let t : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have h1 : t ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one t
  have h2 := congrArg CommaMorphism.left h1
  rw [hw]
  refine Eq.trans ?_ h2
  change _ = Spec.map (Scheme.stalkClosedPointTo z) ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G).left
  refine Eq.trans ?_ (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv)
  have key := spec_dual_fst (Scheme.stalkClosedPointTo z).hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ v.left) key).trans (Category.assoc _ _ _))

theorem eq_sum_of_mem_flagStep {Ω : Type} [Field Ω] {Li : Type} [AddCommGroup Li] [Module Ω Li] {r n : ℕ}
    (hn : n ≤ r) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (hd : ∀ j l, π j (b l) = if j = l then 1 else 0)
    {w : Li} (hw : w ∈ flagStep Ω b n) :
    w = ∑ l : Fin n, π (Fin.castLE hn l) w • b (Fin.castLE hn l) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' : (k : ℕ) < n := hk
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin n)]
    · simp [hd, Fin.castLE]
    · intro l _ hl
      have : Fin.castLE hn l ≠ k := fun e => hl (Fin.ext (by simpa using congrArg Fin.val e))
      simp [hd, this]
    · simp
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp [add_smul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    conv_lhs => rw [hx]
    simp [Finset.smul_sum, mul_smul]

theorem ev_sum {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X} {p : Cpt ξ}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Submodule (regAt ξ p) Li} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ev : L →+ V)
    (hev : ∀ (a : regAt ξ p) (r : ℂ) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) {n : ℕ} (g : Fin n → Li)
    (hg : ∀ l, g l ∈ L) (a : Fin n → Ω) (ha : ∀ l, a l ∈ regAt ξ p) (c : Fin n → ℂ)
    (hc : ∀ l, ValAt ξ z (a l) (c l)) {w : Li} (hw : w ∈ L) (hwe : w = ∑ l, a l • g l) :
    ev ⟨w, hw⟩ = ∑ l, c l • ev ⟨g l, hg l⟩ := by
  have h1 : (⟨w, hw⟩ : L) = ∑ l, (⟨a l, ha l⟩ : regAt ξ p) • (⟨g l, hg l⟩ : L) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hwe
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun l _ => hev _ _ _ (hc l)

theorem gram_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)) (i : Fin r), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (s : ℂ),
      (∀ j, f j ∈ flagStep Ω b i) → e ∈ flagStep Ω b (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      ValAt ξ z (π i e) s → s ≠ 0 → (gramAt h z v).det ≠ 0 →
      (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ -
          Real.log ‖(gramAt h z v).det‖) =
        Real.log ‖s‖ + (1 / 2) * (Real.log ‖(gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det‖ -
          Real.log ‖(gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)).det‖) := by
  intro X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B i hξ hd hreg hB f e v ve s hf he hv hve hs hs0 hdet
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M ℂ z hz Vz MR hξ inferInstance
  obtain ⟨core, hcore⟩ := h.herm z Vz MR
  have val : ∀ {e' : Li} {w : epsAt z ⟶ G}, M.ValAt z e' w →
      ∃ he' : e' ∈ M.lat ⟨centre z, hz⟩, MR.pt (ev ⟨e', he'⟩) = w := by
    intro e' w hw
    obtain ⟨x, rfl⟩ := MR.onto w (tan_of_lieVal hw)
    obtain ⟨he', hx⟩ := (hev1 e' x).1 hw
    exact ⟨he', by rw [hx]⟩
  choose hbL hbB using fun j => val (hB j)
  choose hfL hfv using fun j => val (hv j)
  obtain ⟨heL, hve'⟩ := val hve
  obtain ⟨β, hβ⟩ : ∃ β : Fin (i + 1) → Vz, ∀ l, β l = ev ⟨b (Fin.castLE i.2 l), hbL _⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin i → Vz, ∀ j, x j = ev ⟨f j, hfL j⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨xe, hxe⟩ : ∃ xe : Vz, xe = ev ⟨e, heL⟩ := ⟨_, rfl⟩
  have hi : (i : ℕ) ≤ r := i.2.le
  have hC : ∀ (j : Fin i) (l : Fin r), ∃ c : ℂ, ValAt ξ z (π l (f j)) c :=
    fun j l => val_exists (hreg l _ (hfL j))
  choose C hC using hC
  have hD : ∀ l : Fin r, ∃ c : ℂ, ValAt ξ z (π l e) c := fun l => val_exists (hreg l _ heL)
  choose D hD using hD
  have hsD : D i = s := val_unique hξ (hD i) hs
  have hsum : ∀ j, x j = ∑ l : Fin i, C j (Fin.castLE hi l) • β l.castSucc := by
    intro j
    rw [hx j, ev_sum ev hev2 (fun l : Fin i => b (Fin.castLE hi l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE hi l) (f j)) (fun _ => hreg _ _ (hfL j)) (fun l => C j (Fin.castLE hi l))
      (fun _ => hC _ _) (hfL j) (eq_sum_of_mem_flagStep hi b π hd (hf j))]
    exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
  have hsume : xe = ∑ l : Fin i, D (Fin.castLE hi l) • β l.castSucc + s • β (Fin.last i) := by
    rw [hxe, ev_sum ev hev2 (fun l : Fin (i + 1) => b (Fin.castLE i.2 l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE i.2 l) e) (fun _ => hreg _ _ heL) (fun l => D (Fin.castLE i.2 l))
      (fun _ => hD _) heL (eq_sum_of_mem_flagStep i.2 b π hd he), Fin.sum_univ_castSucc]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
    · rw [hβ, ← hsD]; rfl
  have gr : ∀ {m : ℕ} (u : Fin m → Vz),
      gramAt h z (fun l => MR.pt (u l)) = Matrix.of fun a b => core.inner (u a) (u b) := by
    intro m u
    ext a c
    simp [gramAt, hcore]
  have e1 : v = fun l => MR.pt (x l) := funext fun j => by rw [hx, hfv]
  have e2 : (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G)) =
      fun l => MR.pt ((Fin.snoc x xe : Fin (i + 1) → Vz) l) := by
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp [hxe, hve']
    · simp [e1]
  have e3 : (fun l : Fin (i + 1) => B (Fin.castLE i.2 l)) = fun l => MR.pt (β l) :=
    funext fun l => by rw [hβ, hbB]
  have e4 : (fun l : Fin i => B (Fin.castLE i.2.le l)) = fun l => MR.pt (β l.castSucc) :=
    funext fun l => by rw [hβ, hbB]; rfl
  have hind := GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z hz r b π B hξ hd hreg hB (i + 1) (Fin.castLE i.2)
    (Fin.castLE_injective _)
  change (gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det ≠ 0 at hind
  rw [e3, gr] at hind
  rw [e1, gr] at hdet
  rw [e2, e3, e4, e1, gr, gr, gr, gr]
  exact GlobalTheory.T.gram_det_change_of_basis Vz core i β x xe (Matrix.of fun j l => C j (Fin.castLE hi l))
    (fun l => D (Fin.castLE hi l)) s hsum hsume hs0 hdet hind

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
