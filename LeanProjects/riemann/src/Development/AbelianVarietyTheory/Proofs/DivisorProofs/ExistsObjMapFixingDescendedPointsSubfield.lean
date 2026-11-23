import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointDescendsAlgClosedSubfieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AutLift

theorem spMap_fix (K : Type) [Field K] (k₀ : Subfield K) (σ : K ≃+* K) (h : ∀ a ∈ k₀, σ a = a) :
    spMap (σ : K →+* K) ≫ spMap k₀.subtype = spMap k₀.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x x.2

theorem eta_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {La : Type} [AddCommGroup La] (f : La → (𝟙_ (Over S) ⟶ G))
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : La) : f (n • a) = f a ^ n := by
  have h0 : f 0 = 1 := by
    have := hf 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem exists_objMap_fixing_descended_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Bb : Type} [CommRing Bb] {b : Base l Bb} (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ {s : Sp K ⟶ Sp Bb} (o : Obj D l b s) (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (π : o.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback o.t.G B₀ (spMap k₀.subtype) π → LBIso o.t.PP.L (M₀.pull π) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ n : ObjMap o o (spMap (σ : K →+* K)), ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ → (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ n.toSABMap.φ = spMap (σ : K →+* K) ≫ x := by
  intro E _ _ _ H D l Bb _ b K _ _ _ k₀ hk₀ s o B₀ _ _ M₀ π hB₀ hM₀ hpb hL σ hσ
  haveI : IsAlgClosed k₀ := hk₀
  have hfix := spMap_fix K k₀ σ hσ
  let st : o.t.G.left ⟶ o.t.G.left := hpb.1.lift π (o.t.G.hom ≫ spMap (σ : K →+* K))
    (by rw [hpb.1.w, Category.assoc, hfix])
  have hst₁ : st ≫ π = π := hpb.1.lift_fst _ _ _
  have hst₂ : st ≫ o.t.G.hom = o.t.G.hom ≫ spMap (σ : K →+* K) := hpb.1.lift_snd _ _ _

  have hpt : ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ →
      (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ st = spMap (σ : K →+* K) ≫ x := by
    rintro x hx ⟨x₀, hx₀⟩
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, hx₀, ← Category.assoc, hfix]
    · rw [Category.assoc, hst₂, ← Category.assoc, hx, Category.assoc, hx, Category.id_comp, Category.comp_id]

  have hcart : IsGrpPullback o.t.G o.t.G (spMap (σ : K →+* K)) st :=
    hpb.cancel (hpb.congr hfix.symm hst₁.symm) hst₂

  have hact : ∀ a, (o.t.act.act a).left ≫ st = st ≫ (o.t.act.act a).left := by
    intro a
    obtain ⟨f₀, -, hf₀⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends k₀ K k₀.subtype B₀ B₀ o.t.G o.t.G π π hB₀ hB₀ hpb hpb
      (o.t.act.act a) (o.t.act.hom a)
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, ← hf₀, ← Category.assoc, hst₁, hf₀]
    · rw [Category.assoc, hst₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hst₂]

  have hLB : LBIso o.t.PP.L (o.t.PP.L.pull st) := by
    have h1 : LBIso (o.t.PP.L.pull st) (M₀.pull π) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.t.PP.L st st rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame M₀ _ (fun _ => π) _ st fun _ => hst₁.symm) hL
    exact LBIso.trans o.t.PP.isLB (pull_isLB hM₀ π) (pull_isLB o.t.PP.isLB st) hL (LBIso.symm h1)

  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o.t o.t (spMap (σ : K →+* K)) st o.proper hcart hact hLB
  have hφ : m.cm.F = st := hm

  have hun : η[o.t.G].left ≫ π = spMap k₀.subtype ≫ η[B₀].left := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hpb
  have htor : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (n : ℕ), 0 < n → y ^ n = 1 →
      y.left ≫ st = spMap (σ : K →+* K) ≫ y.left := by
    intro y n hn hy
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o.t.G π hB₀ hpb n hn y η[B₀].left (by
      rw [hy, ← hun]; simp [Hom.one_def])
    refine hpt y.left ?_ ⟨y₀, hy₀⟩
    simpa using Over.w y
  have hMmem : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this
  refine ⟨{ m with
    eta := fun a => by
      rw [hφ]
      refine htor (o.eta a) l.M (by have := l.three_le; omega) ?_
      rw [← eta_nsmul o.eta o.eta_add, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact o.eta_ker _ (Submodule.smul_mem_smul hMmem trivial)
    etaA := fun a => by
      rw [hφ]
      refine htor (o.etaA a) l.A l.A_pos ?_
      rw [← eta_nsmul o.etaA o.etaA_add]
      exact o.etaA_ker a }, fun x hx hx₀ => ?_⟩
  show x ≫ m.cm.F = _
  rw [hφ]
  exact hpt x hx hx₀

end GlobalTheory.AutLift
