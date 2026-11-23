import Development.WeilBound.CoreStatements.FlagImmersions.MemFlagOfRel
import Development.WeilBound.CoreStatements.FlagImmersions.OfForall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement

noncomputable section

namespace RootFieldNumerics.Rig

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem step_coeff {Ω : Type} [Field Ω] {L : Type} [AddCommGroup L] [Module Ω L] (A : Subring Ω) {m : ℕ} {b : Fin m → L}
    (hli : LinearIndependent Ω b) {e : L} (hs : e ∈ Submodule.span A (Set.range b)) {k : ℕ} (hm : e ∈ flagStep Ω b k) :
    ∃ a : Fin m → A, e = ∑ j, (a j : Ω) • b j ∧ ∀ j : Fin m, k ≤ j → (a j : Ω) = 0 := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hs
  have ha' : e = ∑ j, (a j : Ω) • b j := ha.symm
  refine ⟨a, ha', fun j hij => ?_⟩
  obtain ⟨t, hl, e'⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e'
  have h2 : ∑ j, ((a j : Ω) - t j) • b j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← ha', e', sub_self]
  have h4 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  rw [h4]
  by_contra hne
  have h7 : (j : ℕ) < k := hl (Finsupp.mem_support_iff.2 hne)
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y ∅ y}

theorem side (hF : FrameVals) (hG : Top.Given) (hD : 1 ≤ D.p + D.q) (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H)
    {z : Sp ℂ ⟶ 𝔐.X} {p : Sp ℂ ⟶ Y.X} (hp : z ≫ 𝔐.f = p) (hz : 𝔐.Interior z) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mp : LieModel Y.t.G p V) {cs : Fin (labelRk D s) → Fl.Li₀} {α ω : Fin (labelRk D s) → V}
    (hα : ∀ i, Fl.M₀.ValAt p (cs i) (Mp.pt (α i))) (ha : (𝔐.V s).IsFrameAt (fun i => Fl.j (cs i)) ⟨centre z, 𝔐.all _⟩)
    {b : Fin (labelRk D s) → 𝔐.Li} (hb : (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩)
    {v : Fin (labelRk D s) → (epsAt z ⟶ 𝔐.t.G)} (hv : ∀ i, 𝔐.M.ValAt z (b i) (v i))
    (hω : ∀ i, (v i).left ≫ 𝔐.m.φ = (Mp.pt (ω i)).left) {u : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) Ω}
    {uz : Fin (labelRk D s) → Fin (labelRk D s) → ℂ} (hu : ∀ i k, ValAt 𝔐.ξ z (u i k) (uz i k))
    (hfl : ∀ k, flagStep Ω b k = flagStep Ω (fun k => ∑ i, u i k • Fl.j (cs i)) k) :
    LinearIndependent ℂ α ∧ ∀ k : Fin (labelRk D s), ∑ i, uz i k • α i ∈ flagStep ℂ ω (k + 1) := by
  subst hp
  have hξ := 𝔐.tie.gen
  have hall : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  let Mz : LieModel 𝔐.t.G z V := LieMove.pullModel 𝔐.m.cart Mp
  have hlift : ∀ (w : epsAt z ⟶ 𝔐.t.G) (e : V), w.left ≫ 𝔐.m.φ = (Mp.pt e).left → w = Mz.pt e := fun w e h =>
    LieMove.pushEps_inj 𝔐.m.cart ((Over.OverMorphism.ext h).trans (LieMove.push_lift 𝔐.m.cart _).symm)
  have hva : ∀ i, 𝔐.M.ValAt z (Fl.j (cs i)) (Mz.pt (α i)) := fun i => by
    obtain ⟨h1, h2⟩ := (Fl.M₀.exists_valAt_iff _ _).1 ⟨_, hα i⟩
    obtain ⟨w, w', e1, e2, e3⟩ := HodgePull.value_pull (M := Fl.M₀) (M' := 𝔐.M) (j := Fl.j) 𝔐.fn_over 𝔐.m.cart Fl.j_pt hall h1 h2
    rw [e1.unique 𝔐.gen₀ (hα i)] at e3
    exact hlift _ _ e3 ▸ e2
  have hvb : ∀ i, 𝔐.M.ValAt z (b i) (Mz.pt (ω i)) := fun i => hlift _ _ (hω i) ▸ hv i
  constructor
  · obtain ⟨g, Λ, _, _, R, x, hx, -⟩ := GlobalTheory.T.interior_point_lattice_data hG.2.2.2.2.1 E H D l Xo c Y ∅ Ω K J y 𝔐 z hD hz hG _
      (fun i => Mz.pt (α i)) fun i => Mz.tan _
    obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y ∅ Ω K J y 𝔐 ℂ z
    have hi := ((hF hG E H D l Xo c Y Ω K J y 𝔐 z s _ hD hz ha).2 g Λ R σ x _ hσ hva hx).1
    obtain ⟨Rel, r1, r2, -⟩ := exists_rel hx Mz
    exact indep_of_rel r2 (fun i => r1 i _ rfl) hi
  · intro k
    have hmem : ∑ i, u i k • Fl.j (cs i) ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hall⟩) (Set.range b) := by
      rw [← hb.2, ha.2]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨_, t, ht, -⟩ := hu i k
      exact Submodule.smul_mem (Submodule.span (regAt 𝔐.ξ ⟨centre z, hall⟩) (Set.range fun i => Fl.j (cs i)))
        (⟨u i k, t, ht⟩ : regAt 𝔐.ξ ⟨centre z, hall⟩) (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨a, e, a0⟩ := step_coeff _ hb.1 hmem (k := k + 1) (by
      rw [hfl]
      exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩)
    choose r hr using fun j => v_of_reg hall (a j).2
    have e1 := HodgeMetric.valAt_sum_smul 𝔐.M Mz hall Finset.univ _ _ hva (fun i => u i k) (fun i => uz i k) fun i => hu i k
    have e2 := HodgeMetric.valAt_sum_smul 𝔐.M Mz hall Finset.univ _ _ hvb (fun i => (a i : Ω)) r hr
    rw [← e] at e2
    rw [Mz.inj (e1.unique hξ e2)]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k + 1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · have h0 := hr j
      rw [a0 j (not_lt.1 hj)] at h0
      have : r j = 0 := CxVal.unique h0 ⟨hall, 0, map_zero _, map_zero _⟩
      rw [this, zero_smul]
      exact Submodule.zero_mem _

end RootFieldNumerics.Rig

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp RootFieldNumerics.Rig

theorem genRigid_of : FrameVals → GenRigid := by
  intro hF hG E _ _ _ H D l Xo c Y Ω _ K _ J _ y 𝔐 Fl hD hdeg
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cs, u, hc, -, hji, -, h1, h0, hflag, -, -, hfin⟩ := Fl.generic
  rw [hdeg, IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  have hξ := 𝔐.tie.gen
  have P1 := ev_point 𝔐 _ hfin
  have P2 := Ev.all fun s => ev_frame hξ (𝔐.vb s) (hji s) fun i =>
    (Fl.V₀_mem s _).1 ((hc s).2 ▸ Submodule.subset_span ⟨i, rfl⟩)
  have P3 := Ev.all fun q : Σ s, Fin (labelRk D s) × Fin (labelRk D s) => ev_reg hξ (u q.1 q.2.1 q.2.2)
  have P4 := Ev.pull 𝔐 (Ev.all fun q : Σ s, Fin (labelRk D s) =>
    ev_mem 𝔐.gen₀ (Flat.EigVb.lat_isVB_of_smooth Y.t.semi.smooth Fl.M₀) (e := cs q.1 q.2) trivial)
  obtain ⟨U, hU, hP⟩ := P1.and (P2.and (P3.and P4))
  obtain ⟨Q1, Q2, Q3, U₀, Q4, hU₀⟩ := hP U le_rfl
  refine ⟨U, hU, ?_⟩
  intro b z z' p v v' w w' g Λ _ _ R x x' hb hz hz' hi hi' hf hf' hp hp' hv hv' hw hw' hR hx
  obtain ⟨V, _, _, ⟨Mp⟩⟩ := lieModel_exists Y.X Y.t.G ℂ p
  have htan : ∀ {z : Sp ℂ ⟶ 𝔐.X} (_ : z ≫ 𝔐.f = p) (v : epsAt z ⟶ 𝔐.t.G) (w : epsAt p ⟶ Y.t.G), IsTanAt 𝔐.t.G z v →
      v.left ≫ 𝔐.m.φ = w.left → ∃ e, Mp.pt e = w := by
    intro z hp v w ht e
    subst hp
    have e' : LieMove.pushEps 𝔐.m.cart v = w := Over.OverMorphism.ext e
    exact Mp.onto _ (e' ▸ (LieMove.tan_iff 𝔐.m.cart v).1 ht)
  choose ω hω using fun a => htan hp (v a) (w a) (hv a).isTanAt (hw a)
  choose ω' hω' using fun a => htan hp' (v' a) (w' a) (hv' a).isTanAt (hw' a)
  have hα : ∀ q : Σ s, Fin (labelRk D s), ∃ e, Fl.M₀.ValAt p (cs q.1 q.2) (Mp.pt e) := fun q => by
    subst hp
    obtain ⟨w₀, hw₀⟩ := (Fl.M₀.exists_valAt_iff (z ≫ 𝔐.f) (cs q.1 q.2)).2
      ⟨spec_f 𝔐 z, Q4 q ⟨_, spec_f 𝔐 z⟩ (hU₀ _ hz)⟩
    obtain ⟨e, rfl⟩ := Mp.onto _ hw₀.isTanAt
    exact ⟨e, hw₀⟩
  choose α hα using hα
  choose uz huz using fun s i k => v_of_reg (𝔐.all (centre z)) (Q3 ⟨s, i, k⟩ ⟨_, 𝔐.all _⟩ hz)
  choose uz' huz' using fun s i k => v_of_reg (𝔐.all (centre z')) (Q3 ⟨s, i, k⟩ ⟨_, 𝔐.all _⟩ hz')
  obtain ⟨Rel, r1, -, r3⟩ := exists_rel hR Mp
  have hone : ∀ {z : Sp ℂ ⟶ 𝔐.X} {a : Ω} {r : ℂ}, ValAt 𝔐.ξ z a r → a = 1 → r = 1 := fun h e =>
    CxVal.unique (e ▸ h) (CxVal.one (𝔐.all _))
  have hzero : ∀ {z : Sp ℂ ⟶ 𝔐.X} {a : Ω} {r : ℂ}, ValAt 𝔐.ξ z a r → a = 0 → r = 0 := fun h e =>
    CxVal.unique (e ▸ h) ⟨𝔐.all _, 0, map_zero _, map_zero _⟩
  have key : ∀ s, uz s = uz' s := fun s => by
    obtain ⟨i1, m1⟩ := side hF hG hD Fl s hp hi Mp (fun i => hα ⟨s, i⟩) (Q2 s ⟨_, 𝔐.all _⟩ hz) (hf s) (fun i => hv ⟨s, i⟩)
      (ω := fun i => ω ⟨s, i⟩) (fun i => by rw [hω]; exact hw _) (huz s) fun k => (hb s k).trans (hflag s k)
    obtain ⟨-, m2⟩ := side hF hG hD Fl s hp' hi' Mp (fun i => hα ⟨s, i⟩) (Q2 s ⟨_, 𝔐.all _⟩ hz') (hf' s) (fun i => hv' ⟨s, i⟩)
      (ω := fun i => ω' ⟨s, i⟩) (fun i => by rw [hω']; exact hw' _) (huz' s) fun k => (hb s k).trans (hflag s k)
    refine tri_unique i1 (fun k => hone (huz s k k) (h1 s k)) (fun i k h => hzero (huz s i k) (h0 s i k h))
      (fun k => hone (huz' s k k) (h1 s k)) (fun i k h => hzero (huz' s i k) (h0 s i k h)) m1 fun k => ?_
    exact flag_le_of_rel r3 (fun i => r1 (.inl ⟨s, i⟩) _ (hω _).symm) (fun i => r1 (.inr ⟨s, i⟩) _ (hω' _).symm)
      (hx s _) (m2 k)
  refine Q1 z z' hz hz' (hp.trans hp'.symm) ?_
  rintro _ ⟨⟨s, i, k⟩, rfl⟩
  exact ⟨_, huz s i k, key s ▸ huz' s i k⟩

end RootFieldNumerics
