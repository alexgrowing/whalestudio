import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevMoveFibre

theorem alg {R : Type} [CommRing R] {La : Type} [AddCommGroup La] [Module R La] {Q : Type} [Group Q]
    (Mb Mc : Ideal R) (M : ℕ) (hcop : Mb ⊔ Mc = ⊤) (hMb : (M : R) ∈ Mb) (hMc : (M : R) ∈ Mc)
    (act : R → Q → Q) (ev evM : La → Q) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hker : ∀ a ∈ Mb • (⊤ : Submodule R La), ev a = 1) (hag : ∀ a ∈ Mc • (⊤ : Submodule R La), ev a = evM a)
    (Ilin : ∀ (c : R) a, evM (c • a) = act c (evM a)) (Iker : ∀ a, evM a = 1 ↔ ∃ b, a = M • b)
    (Ionto : ∀ q : Q, q ^ M = 1 ↔ ∃ a, evM a = q) (hpow : ∀ q, act (M : R) q = q ^ M) :
    (∀ c a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ a ∈ Mb • (⊤ : Submodule R La)) ∧
      (∀ q, (∀ c ∈ Mb, act c q = 1) → ∃ a, ev a = q) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : R) ∈ Mb ⊔ Mc)
  have hsplit : ∀ a : La, a = u • a + v • a := fun a => by rw [← add_smul, huv, one_smul]
  have hdec : ∀ a, ev a = evM (v • a) := fun a => by
    conv_lhs => rw [hsplit a]
    rw [hadd, hker _ (Submodule.smul_mem_smul hu trivial), _root_.one_mul,
      hag _ (Submodule.smul_mem_smul hv trivial)]
  have hMs : ∀ (I : Ideal R), (M : R) ∈ I → ∀ b : La, M • b ∈ I • (⊤ : Submodule R La) := fun I hI b => by
    rw [← Nat.cast_smul_eq_nsmul R]; exact Submodule.smul_mem_smul hI trivial
  refine ⟨fun c a => ?_, fun a => ⟨fun h => ?_, hker a⟩, fun q hq => ?_⟩
  · rw [hdec, hdec, smul_comm, Ilin]
  · rw [hdec, Iker] at h
    obtain ⟨b, hb⟩ := h
    rw [hsplit a, hb]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) (hMs Mb hMb b)
  · obtain ⟨b, hb⟩ := (Ionto q).1 (by rw [← hpow]; exact hq _ hMb)
    have hub : evM (u • b) = 1 := by rw [Ilin, hb]; exact hq u hu
    obtain ⟨b', hb'⟩ := (Iker _).1 hub
    have hmem : b ∈ Mc • (⊤ : Submodule R La) := by
      rw [hsplit b, hb']
      exact Submodule.add_mem _ (hMs Mc hMc b') (Submodule.smul_mem_smul hv trivial)
    exact ⟨b, (hag b hmem).trans hb⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (h : f = f')
    (n : SABMap t' t f) : ∃ n' : SABMap t' t f', n'.φ = n.φ := by
  subst h; exact ⟨n, rfl⟩

theorem iterate_eq {C : Type*} [Category C] {X : C} (θ : Aut X) (N : ℕ) :
    (fun f : X ⟶ X => f ≫ θ.hom)^[N] (𝟙 X) = (θ ^ N).hom := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

theorem act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (α : OAct (𝓞 E) G)
    (q : T ⟶ G) (n : ℕ) : q ≫ α.act (n : 𝓞 E) = q ^ n := by
  have h0 : α.act 0 = 1 := by
    have : α.act 0 * α.act 0 = α.act 0 * 1 := by rw [_root_.mul_one, ← α.add, add_zero]
    exact mul_left_cancel this
  induction n with
  | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
  | succ n ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]

theorem sec_move {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hc : IsGrpPullback G' G f φ) (e e' : 𝟙_ (Over S') ⟶ G') (ψ : G' ⟶ G')
    (ν : G.left ⟶ G.left) (ρ : S ⟶ S) (hψ : ψ.left ≫ φ = φ ≫ ν) (a b : 𝟙_ (Over S) ⟶ G)
    (he : e.left ≫ φ = f ≫ a.left) (he' : e'.left ≫ φ = f ≫ b.left) (hab : a.left ≫ ν = ρ ≫ b.left)
    (hf : f ≫ ρ = f) : e ≫ ψ = e' := by
  apply Over.OverMorphism.ext
  apply hc.1.hom_ext
  · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, he, Category.assoc, hab, ← Category.assoc, hf, he']
  · exact (Over.w _).trans (Over.w _).symm

end GlobalTheory.LevMoveFibre

open GlobalTheory.LevMoveFibre in

theorem GlobalTheory.LevMoveFibre.exists_fibreAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (x : Sp ℂ ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), Formalism.L2.Pj.IsLevMove ρ ν gM gA → x ≫ ρ = x → ∃ (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N : ℕ) (ev : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), IsMonHom θ ∧ 0 < N ∧ (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A ∧ (∀ a, act.act a ≫ θ = θ ≫ act.act a) ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act.act c) ∧ (∀ a, ev a = 1 ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (∀ c ∈ l.Mb, q ≫ act.act c = 1) → ∃ a, ev a = q) ∧ ∀ a, ev (gM a) ≫ θ = ev a := by
  intro E _ _ _ H Dw l Xo x ρ ν gM gA hlev hx
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨T, hT, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ (GlobalTheory.ModelCompare.objOfSABMap Xo.univ m)
  obtain rfl : T.t = t' := hT
  obtain ⟨n₀, hn₀⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Xo.univ.t T.t ρ x ν m
  obtain ⟨n, hn⟩ := exists_cast hx n₀
  obtain ⟨ψ, hψ, hφ, hact, -⟩ := sabMap_iso n m rfl rfl
  let θ : Aut T.t.G := ψ
  have hL := GlobalTheory.lawsFieldsSeparately
  obtain ⟨N, hN, hθN⟩ := GlobalTheory.AutFin.exists_pow_eq_one hL.2.2.2.2.2.1 hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m n θ hφ
  let o := GlobalTheory.ModelCompare.objOfSABMap Xo.univ m
  have hev : ∀ a, (o.eta a).left ≫ m.φ = x ≫ (Xo.univ.eta a).left := fun a =>
    (GlobalTheory.ModelCompare.objMapOfSABMap Xo.univ m).eta a
  obtain ⟨β, hβ⟩ : ∃ β : KA l →+* ℂ, x ≫ Xo.s = spMap β := ⟨(Spec.preimage (x ≫ Xo.s)).hom, by simp [spMap]⟩
  obtain ⟨-, I, -, -, hM⟩ := o.geom ℂ (𝟙 _) β (by rw [Category.id_comp]; exact hβ)
  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = I.ev l.M a := by
    intro a ha
    have := hM a ha
    rw [show toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) from toUnit_unique _ _] at this
    exact (Category.id_comp _).symm.trans this
  have hMM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have i1 : ∀ (c : 𝓞 E) (a : Dw.La), I.ev l.M (c • a) = I.ev l.M a ≫ T.t.act.act c := I.lin l.M
  have i2 : ∀ a, I.ev l.M a = 1 ↔ ∃ b, a = l.M • b := I.ker l.M hM0
  have i3 : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ^ l.M = 1 ↔ ∃ a, I.ev l.M a = q := I.onto l.M hM0
  have e1 : ∀ a b, o.eta (a + b) = o.eta a * o.eta b := o.eta_add
  have e2 : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = 1 := o.eta_ker
  have e3 : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ≫ T.t.act.act ((l.M : ℕ) : 𝓞 E) = q ^ l.M := fun q => act_natCast _ q _
  let evM : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ T.t.G) := I.ev l.M
  have hM'' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = evM a := hM'
  have i1' : ∀ (c : 𝓞 E) (a : Dw.La), evM (c • a) = (fun c g => g ≫ T.t.act.act c) c (evM a) := i1
  have i2' : ∀ a, evM a = 1 ↔ ∃ b, a = l.M • b := i2
  have i3' : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ^ l.M = 1 ↔ ∃ a, evM a = q := i3
  have hMb : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) hMM
  have hMc : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := (Ideal.mul_le_right : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) hMM
  obtain ⟨hlin, hker, honto⟩ := alg (R := 𝓞 E) (La := Dw.La) (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G) l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) l.M l.coprime hMb hMc (fun c g => g ≫ T.t.act.act c) o.eta evM e1 e2 hM'' i1' i2' i3' e3
  refine ⟨T.pol, T.t.act, ψ.hom, N, o.eta, hψ, hN, ?_, hact, e1, hlin, hker, honto, fun a => ?_⟩
  · rw [iterate_eq θ N, hθN]; rfl
  · exact sec_move m.cart (o.eta (gM a)) (o.eta a) ψ.hom ν.φ ρ (hφ.trans (hn.trans hn₀)) _ _ (hev _) (hev _)
      (hlev.2.1 a) hx
