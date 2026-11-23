import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di

structure Steps : Prop where
  ring : RingL
  geoPB : GeoPB
  geoM : GeoM
  c1BC : FirstChernClassBaseChange
  rootNat : RootNat
  powRoot : PowRoot
  untw : Untw
  lim : PBLim
  pbq : PBQOf
  sq : DiagSq
  clear : Clear
  blowBC : G.BlowBC
  blowE : G.BlowE
  pbe : G.PBE

theorem neg_sub (hI : In) (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (hn : n < 0) : Subsingleton (V l X n) := by
  have h : Subsingleton (Hl l (sch.obj X) n 0) :=
    ⟨fun a b => Subtype.ext (funext fun j => ((hI.a9 (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn).elim _ _)⟩
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | add a b ha hb => rw [ha, hb, add_zero]
  | tmul a x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]

theorem pull_untw (hI : In) (q : ℕ) [NeZero q] {E X : Scheme.{0}} (j : E ⟶ X) (x : Ht q (sch.obj X) 2 1)
    (ρ : Ht q (sch.obj X) 0 (-1)) :
    pull _ (sch.map j) _ 2 (untw q x ρ) = untw q (pull _ (sch.map j) _ 2 x) (pull _ (sch.map j) _ 0 ρ) := by
  have key : ∀ (n i : ℤ) (hn : 2 + 0 = n) (hi : 1 + -1 = i), pull _ (sch.map j) (tw q i) n ((cup q x ρ).cast hn hi) =
      (cup q (pull _ (sch.map j) _ 2 x) (pull _ (sch.map j) _ 0 ρ)).cast hn hi := by
    rintro _ _ rfl rfl
    exact (hI.a6nat q).1 (sch.map j) x ρ
  exact key _ _ _ _

theorem untw_zero (q : ℕ) {X : Scheme.{0}} (ρ : Ht q (sch.obj X) 0 (-1)) : untw q 0 ρ = 0 := by
  have key : ∀ (n i : ℤ) (hn : 2 + 0 = n) (hi : 1 + -1 = i),
      (cup q (0 : Ht q (sch.obj X) 2 1) ρ).cast hn hi = 0 := by
    rintro _ _ rfl rfl
    rw [map_zero]
    rfl
  exact key _ _ _ _

theorem Steps.core (H : Steps) (hI : In) (hQ : QDiag) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k]
    (hl : (l : k) ≠ 0) (d : ℕ) (hd : 1 ≤ d) {X P W : Scheme.{0}} (p : X ⟶ S k) (p₁ p₂ : P ⟶ X) (Δ : X ⟶ P)
    (hP : IsPullback p₁ p₂ p p) (h₁ : Δ ≫ p₁ = 𝟙 _) (h₂ : Δ ≫ p₂ = 𝟙 _) (hp : SP (d + 1) p) (hpr : IsProj p) (π : W ⟶ P)
    (hπ : IsProper π) (D : CrystallineSemistableComparison.E.LineData W) (hB : Nonempty (Blow (p₁ ≫ p) Δ π D (d + 1)))
    (ζ : ∀ n, Prim (l ^ n) Γ(S k, ⊤)) (x : ∀ n, Ht (l ^ n) (sch.obj W) 2 1) (hx : ∀ n, IsFirstChernClassOfLineBundle (l ^ n) D (x n))
    (v : Hl l (sch.obj W) 2 0)
    (hv : ∀ n, v.1 n = Di.untw (l ^ n) (x n) (rootClass (-1) ((ζ n).map (π ≫ p₁ ≫ p).appTop.hom))) :
    DiagL l d p₁ p₂ π v := by
  have hR := H.ring hI l
  have hlX : IsUnit (l : Γ(X, ⊤)) := LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)
  have hs := hp.2
  have hs1 : SmoothOfRelativeDimension (d + 1) p₁ :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (d + 1)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (d + 1)) hP.flip hs
  have hpb := IsPullback.of_hasPullback π Δ
  obtain ⟨hi, hr⟩ := H.blowE k (p₁ ≫ p) Δ π D d (d + 1) hB inferInstance hπ _ _ hpb
  have hcl := hi.cl
  let U : W.Opens := ⟨(Set.range (pullback.fst π Δ))ᶜ, (pullback.fst π Δ).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Off (pullback.fst π Δ) U := rfl
  have hE : ∀ n, PBT (l ^ n) (d + 1) (pullback.snd π Δ) (pull _ (sch.map (pullback.fst π Δ)) _ 2 (x n)) ∧
      pull _ (sch.map U.ι) _ 2 (x n) = 0 := fun n => by
    have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨L, hL, hxL⟩ := hx n
    have h := H.pbe hI (l ^ n) k (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) (p₁ ≫ p) Δ π D (d + 1) hB _ _ hpb
      L hL (x n) hxL
    exact ⟨h.1, h.2 U hU⟩
  have hcomp : pullback.fst π Δ ≫ π ≫ p₁ ≫ p = pullback.snd π Δ ≫ p := by
    rw [pullback.condition_assoc, reassoc_of% h₁]
  have h0 : pb l U.ι 2 (toV v) = 0 := by
    have : pullHl l (sch.map U.ι) 2 0 v = 0 := Subtype.ext (funext fun n => by
      have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      change pull _ (sch.map U.ι) _ 2 (v.1 n) = 0
      rw [hv n, pull_untw hI, (hE n).2, untw_zero])
    rw [LRingPf.pb_tmul, this, TensorProduct.tmul_zero]
  have hPB : PBQ l (pullback.snd π Δ) (pb l (pullback.fst π Δ) 2 (toV v)) := by
    rw [LRingPf.pb_tmul]
    refine H.pbq l hR (neg_sub hI l) (d + 1) (by omega) _ hlX _ (H.lim hI l hR (d + 1) _ hlX _ fun n => ?_)
    have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have h := H.untw hI H.rootNat H.powRoot (l ^ n) (d + 1) _ ((ζ n).map p.appTop.hom) _ (hE n).1
    have e : ((ζ n).map p.appTop.hom).map (pullback.snd π Δ).appTop.hom =
        ((ζ n).map (π ≫ p₁ ≫ p).appTop.hom).map (pullback.fst π Δ).appTop.hom := Subtype.ext (by
      change (p.appTop ≫ (pullback.snd π Δ).appTop).hom (ζ n).1 = ((π ≫ p₁ ≫ p).appTop ≫ (pullback.fst π Δ).appTop).hom (ζ n).1
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hcomp])
    rw [e, ← H.rootNat, ← pull_untw hI, ← hv n] at h
    exact h
  exact H.clear hI l hR d p₁ p₂ π hlX v
    (H.sq hQ l k hl hR d p p₁ p₂ Δ hP h₁ h₂ hp hpr π _ _ _ hpb hi hr U hU _ h0 hPB)

set_option maxHeartbeats 1000000 in
theorem Steps.diagEt2 (H : Steps) (hI : In) (hQ : QDiag) : DiagEt2 := by
  intro l _ K _ M d hd hM hs T r v hv
  obtain ⟨D', τ, L, x, hBC, hL, hx, hvx⟩ := hv
  have hl : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨g1, g2⟩ := H.geoPB K (PadicAlgCl l)
  obtain ⟨m1, m2, m3⟩ := H.geoM l K
  obtain ⟨hp, hpr⟩ := m1 M (d + 1) hM hs
  have hP := g2 M.q T.P.q _ _ (Model.genMap_q T.p₁ T.h₁) (Model.genMap_q T.p₂ T.h₂) (m3 M T.P T.p₁ T.p₂ T.h₁ T.h₂ T.prod)
  have hΔ := g1 M.q T.P.q _ (Model.genMap_q T.Δ T.hΔ)
  have hπ := g1 T.Y.q T.P.q _ (Model.genMap_q T.π T.hπ)
  have hB := H.blowBC K (PadicAlgCl l) (algebraMap K _) _ _ _ _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback T.P.q _) hΔ hπ T.blow
  have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) T.P.q _ (Model.genMap_q T.p₁ T.h₁) ≫ pullback.snd M.q _ = pullback.snd T.P.q _ :=
    pullback.lift_snd _ _ _
  have e2 : GlobalTheory.Et.geomMap (PadicAlgCl l) T.Y.q _ (Model.genMap_q T.π T.hπ) ≫ pullback.snd T.P.q _ = pullback.snd T.Y.q _ :=
    pullback.lift_snd _ _ _
  have hsec : ∀ (u : T.P.X ⟶ M.X) (hu : u ≫ M.p = T.P.p), T.Δ ≫ u = 𝟙 _ →
      GlobalTheory.Et.geomMap (PadicAlgCl l) M.q _ (Model.genMap_q T.Δ T.hΔ) ≫
        GlobalTheory.Et.geomMap (PadicAlgCl l) T.P.q _ (Model.genMap_q u hu) = 𝟙 _ := fun u hu h => by
    have h' : Model.genMap T.Δ T.hΔ ≫ Model.genMap u hu = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, h, Category.comp_id, Category.id_comp]
      · simp only [Model.genMap, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, h', Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]
  have hpro : IsProper (GlobalTheory.Et.geomMap (PadicAlgCl l) T.Y.q _ (Model.genMap_q T.π T.hπ)) :=
    MorphismProperty.of_isPullback (P := @IsProper) hπ (m2 T.Y T.P T.π T.hπ T.smY T.smP)
  rw [← e1] at hB
  exact H.core hI hQ l (PadicAlgCl l) hl d hd _ _ _ _ hP (hsec _ _ T.Δ₁) (hsec _ _ T.Δ₂) hp hpr _ hpro _ hB
    (fun n => (r.ρ n).map (CrystallineSemistableComparison.E.toΓ _)) x
    (fun n => by
      have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      exact H.c1BC hI (l ^ n) T.D _ _ D' τ hBC
        (LPdCut.unit_of (pullback.snd T.Y.q _) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _)) (x n) ⟨L, hL, hx n⟩)
    v (fun n => by rw [e1, e2]; exact hvx n)

end UpperTheory.Gal.KunnethLefschetz.Di
