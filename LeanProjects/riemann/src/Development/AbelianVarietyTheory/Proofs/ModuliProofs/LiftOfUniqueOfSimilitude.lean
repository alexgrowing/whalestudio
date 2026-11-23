import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LiftAut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have hM := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at hM
  exact (Submodule.mem_inf.1 (SetLike.le_def.mp Ideal.mul_le_inf hM)).1

theorem mem_of_modN (l : Level H) {x : D.La} (h : D.ModN l.M x) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨c, rfl⟩ := h
  have hc : l.M • c = (l.M : 𝓞 E) • c := (Nat.cast_smul_eq_nsmul (𝓞 E) l.M c).symm
  rw [hc]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

section

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := by
  have hsplit : x = y + (x - y) := by abel
  rw [hsplit, o.eta_add, o.eta_ker _ h, _root_.mul_one]

theorem etaA_congr (o : Obj D l b s) {x y : D.La} (h : D.ModN l.A (x - y)) :
    o.etaA x = o.etaA y := by
  obtain ⟨c, hc⟩ := h
  have hsplit : x = y + l.A • c := by rw [← hc]; abel
  rw [hsplit, o.etaA_add, o.etaA_ker, _root_.mul_one]

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 :=
  o.eta_ker 0 (Submodule.zero_mem _)

theorem etaA_nsmul (o : Obj D l b s) (n : ℕ) (x : D.La) : o.etaA (n • x) = o.etaA x ^ n := by
  induction n with
  | zero =>
    have h0 : o.etaA 0 = 1 := by simpa using o.etaA_ker 0
    simpa using h0
  | succ k ih => rw [succ_nsmul, o.etaA_add, ih, pow_succ]

theorem mem_of_eta_eq_one (o : Obj D l b s) [Nonempty S] {x : D.La} (h : o.eta x = 1) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨p⟩ := ‹Nonempty S›
  let k := AlgebraicClosure (S.residueField p)
  let y : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) k)) ≫ S.fromSpecResidueField p
  obtain ⟨β, hβ⟩ : ∃ β : B →+* k, y ≫ s = spMap β := by
    refine ⟨(Spec.preimage (y ≫ s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))).hom, ?_⟩
    change _ = Spec.map (CommRingCat.ofHom _)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨-, I, -, -, hev⟩ := o.geom k y β hβ
  have hx : x ∈ (⊤ : Ideal (𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by simp
  rw [← l.coprime, Submodule.sup_smul, Submodule.mem_sup] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hv1 : o.eta v = o.eta 0 := by
    rw [eta_zero, ← h, o.eta_add, o.eta_ker u hu, _root_.one_mul]
  have hev1 : I.ev l.M v = 1 := by
    rw [← hev v hv, hv1, hev 0 (Submodule.zero_mem _), (I.ker l.M hM0 0).2 ⟨0, by simp⟩]
  obtain ⟨c, hc⟩ := (I.ker l.M hM0 v).1 hev1
  exact Submodule.add_mem _ hu (mem_of_modN l ⟨c, hc⟩)

private theorem exists_sabMap_phi_eq_of_eq {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S}
    (e : f = g) (m : SABMap t' t f) : ∃ m' : SABMap t' t g, m'.φ = m.φ := by
  subst e
  exact ⟨m, rfl⟩

private theorem exists_inverse_sabMap_id {S : Scheme.{0}} {t t' : SAB H S} (m : SABMap t' t (𝟙 S)) :
    ∃ m₁ : SABMap t t' (𝟙 S), m.φ ≫ m₁.φ = 𝟙 _ ∧ m₁.φ ≫ m.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := exists_sabMap_phi_eq_of_eq (Category.id_comp (𝟙 S)).symm i
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  obtain ⟨j, hj⟩ := GlobalTheory.ObjMaps.exists_sab_id t'
  obtain ⟨j', hj'⟩ := exists_sabMap_phi_eq_of_eq (Category.id_comp (𝟙 S)).symm j
  obtain ⟨m₃, hm₃⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₁ j'
  have e1 : m₁.φ ≫ m.φ = 𝟙 _ := by rw [← hm₁, hi', hi]
  have e2 : m₃.φ ≫ m₁.φ = 𝟙 _ := by rw [← hm₃, hj', hj]
  have e3 : m.φ = m₃.φ := by
    calc m.φ = (m₃.φ ≫ m₁.φ) ≫ m.φ := by rw [e2, Category.id_comp]
      _ = m₃.φ := by rw [Category.assoc, e1, Category.comp_id]
  exact ⟨m₁, by rw [e3, e2], e1⟩

private theorem etaA_pow_A' (o : Obj D l b s) (a : D.La) : o.etaA a ^ l.A = o.etaA 0 := by
  rw [← etaA_nsmul]
  exact etaA_congr o ⟨a, sub_zero _⟩

end

theorem exists_levEnd {l : Level H} (Xo : Moduli D l) (hpq : 1 ≤ D.p + D.q) (ω : Sim D)
    (hA : (l.A : ℤ) ∣ ω.ν l.A - 1) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), f ≫ Xo.s = Xo.s ∧
      (∀ a, (Xo.univ.eta (ω.f l.M a)).left ≫ m.φ = f ≫ (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA (ω.f l.A a)).left ≫ m.φ = f ≫ (Xo.univ.etaA a).left := by
  have hsm : Smooth Xo.s := Xo.smooth.smooth
  have hred : IsReduced Xo.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ Xo.X Xo.s hsm).1
  obtain ⟨o', m0, he, heA⟩ := GlobalTheory.exists_obj_twist_by_similitude GlobalTheory.SimAlg.sim_group E H D l _ (baseKA l)
    Xo.X Xo.s Xo.univ ω hpq hA
  obtain ⟨f, ⟨hf, ⟨mm⟩⟩, -⟩ := Xo.rep Xo.X Xo.s hred o'
  obtain ⟨m1, hinv, -⟩ := exists_inverse_sabMap_id m0
  obtain ⟨c, hc⟩ := GlobalTheory.ObjMaps.exists_sab_comp mm.toSABMap m1
  obtain ⟨c', hc'⟩ := exists_sabMap_phi_eq_of_eq (Category.id_comp f) c
  refine ⟨f, c', hf, fun a => ?_, fun a => ?_⟩
  · rw [hc', hc, ← he a, Category.assoc, ← Category.assoc m0.φ, hinv, Category.id_comp]
    exact mm.eta a
  · rw [hc', hc, ← heA a, Category.assoc, ← Category.assoc m0.φ, hinv, Category.id_comp]
    exact mm.etaA a

theorem eq_id {l : Level H} (Xo : Moduli D l) (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f)
    (hf : f ≫ Xo.s = Xo.s) (h : ∀ a, (Xo.univ.eta a).left ≫ m.φ = f ≫ (Xo.univ.eta a).left)
    (hA : ∀ a, (Xo.univ.etaA a).left ≫ m.φ = f ≫ (Xo.univ.etaA a).left) : f = 𝟙 _ := by
  have hsm : Smooth Xo.s := Xo.smooth.smooth
  have hred : IsReduced Xo.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ Xo.X Xo.s hsm).1
  obtain ⟨f0, -, huniq⟩ := Xo.rep Xo.X Xo.s hred Xo.univ
  obtain ⟨mid, -⟩ := (GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ (baseKA l) (baseKA l) (baseKA l)
    Xo.X Xo.X Xo.X Xo.s Xo.s Xo.s Xo.univ Xo.univ Xo.univ).1
  have h1 : f = f0 := huniq f ⟨hf, ⟨⟨m, h, hA⟩⟩⟩
  have h2 : 𝟙 Xo.X = f0 := huniq (𝟙 _) ⟨Category.id_comp _, ⟨mid⟩⟩
  rw [h1, h2]

theorem comp_eq_id {l : Level H} (Xo : Moduli D l) (ω ω' : Sim D)
    (hM : ∀ a, D.ModN l.M (ω.f l.M (ω'.f l.M a) - a)) (hA : ∀ a, D.ModN l.A (ω.f l.A (ω'.f l.A a) - a))
    (f f' : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f) (m' : SABMap Xo.univ.t Xo.univ.t f')
    (hf : f ≫ Xo.s = Xo.s) (hf' : f' ≫ Xo.s = Xo.s)
    (h : ∀ a, (Xo.univ.eta (ω.f l.M a)).left ≫ m.φ = f ≫ (Xo.univ.eta a).left)
    (h' : ∀ a, (Xo.univ.eta (ω'.f l.M a)).left ≫ m'.φ = f' ≫ (Xo.univ.eta a).left)
    (k : ∀ a, (Xo.univ.etaA (ω.f l.A a)).left ≫ m.φ = f ≫ (Xo.univ.etaA a).left)
    (k' : ∀ a, (Xo.univ.etaA (ω'.f l.A a)).left ≫ m'.φ = f' ≫ (Xo.univ.etaA a).left) : f ≫ f' = 𝟙 _ := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m' m
  refine eq_id Xo (f ≫ f') n (by rw [Category.assoc, hf', hf]) (fun a => ?_) (fun a => ?_)
  · calc (Xo.univ.eta a).left ≫ n.φ
        = (Xo.univ.eta (ω.f l.M (ω'.f l.M a))).left ≫ m.φ ≫ m'.φ := by
          rw [hn, eta_congr Xo.univ (mem_of_modN l (hM a))]
      _ = f ≫ (Xo.univ.eta (ω'.f l.M a)).left ≫ m'.φ := by rw [← Category.assoc, h, Category.assoc]
      _ = (f ≫ f') ≫ (Xo.univ.eta a).left := by rw [h', Category.assoc]
  · calc (Xo.univ.etaA a).left ≫ n.φ
        = (Xo.univ.etaA (ω.f l.A (ω'.f l.A a))).left ≫ m.φ ≫ m'.φ := by
          rw [hn, etaA_congr Xo.univ (hA a)]
      _ = f ≫ (Xo.univ.etaA (ω'.f l.A a)).left ≫ m'.φ := by rw [← Category.assoc, k, Category.assoc]
      _ = (f ≫ f') ≫ (Xo.univ.etaA a).left := by rw [k', Category.assoc]

theorem exists_levAut {l : Level H} (Xo : Moduli D l) (hpq : 1 ≤ D.p + D.q) (ω : Sim D)
    (hA : (l.A : ℤ) ∣ ω.ν l.A - 1) : ∃ ρ : Xo.X ≅ Xo.X, Xo.LevAut ω ρ := by
  obtain ⟨a0, b0, hab⟩ := GlobalTheory.SimAlg.exists_form_eq_one (D := D) hpq
  obtain ⟨ω', hω'⟩ := GlobalTheory.SimAlg.exists_inv ω hab
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hA0 : 0 < l.A := l.A_pos
  have hA' : (l.A : ℤ) ∣ ω'.ν l.A - 1 := by
    have h2 := (hω' l.A hA0).2
    have e : ω'.ν l.A - 1 = (ω.ν l.A * ω'.ν l.A - 1) - (ω.ν l.A - 1) * ω'.ν l.A := by ring
    rw [e]
    exact dvd_sub h2 (dvd_mul_of_dvd_left hA _)
  obtain ⟨f, m, hf, h, k⟩ := exists_levEnd Xo hpq ω hA
  obtain ⟨f', m', hf', h', k'⟩ := exists_levEnd Xo hpq ω' hA'
  have e1 := comp_eq_id Xo ω ω' (fun a => ((hω' l.M hM0).1 a).2) (fun a => ((hω' l.A hA0).1 a).2)
    f f' m m' hf hf' h h' k k'
  have e2 := comp_eq_id Xo ω' ω (fun a => ((hω' l.M hM0).1 a).1) (fun a => ((hω' l.A hA0).1 a).1)
    f' f m' m hf' hf h' h k' k
  exact ⟨⟨f, f', e1, e2⟩, hf, m, h, k⟩

theorem lift_of_unique_of_similitude (hU : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ)
    (hS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (A : ℕ) (g : D.La →ₗ[𝓞 E] D.La), 1 ≤ D.p + D.q → 0 < A → A.Coprime l.M → (∀ x, g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) → ∃ ω : Sim D, (∀ x, ω.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ (∀ x, D.ModN A (ω.f A x - x)) ∧ (A : ℤ) ∣ ω.ν A - 1) :
    Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → l₁.A.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k) → r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → ∃ (r₁ : (Xo l₁).X ≅ (Xo l₁).X) (ν₁ : SABMap (Xo l₁).univ.t (Xo l₁).univ.t r₁.hom), r₁.hom ≫ (Xo l₁).s = (Xo l₁).s ∧ r₁.hom ≫ r = r ≫ r₀.hom ∧ ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ ∧ ∀ x, ((Xo l₁).univ.etaA x).left ≫ ν₁.φ = r₁.hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL1 hL2 hL3 E _ _ _ H D Xo hpq l₀ l₁ r ν r₀ ν₀ g hA0 hM hMb hcop hlev hk hr₀ hg
  obtain ⟨kk, -, hks⟩ := hk
  have hred : ∀ l : Level H, IsReduced (Xo l).X := fun l =>
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ (Xo l).X (Xo l).s (Xo l).smooth.smooth).1
  rcases isEmpty_or_nonempty (Xo l₀).X with h0 | h0
  · have h1 : IsEmpty (Xo l₁).X := ⟨fun x => h0.false (r.base x)⟩
    have hG : IsEmpty (Xo l₁).univ.t.G.left := ⟨fun x => h1.false ((Xo l₁).univ.t.G.hom.base x)⟩
    obtain ⟨i, hi⟩ := GlobalTheory.ObjMaps.exists_sab_id (Xo l₁).univ.t
    refine ⟨Iso.refl _, i, Category.id_comp _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _, fun x => ?_⟩
    rw [hi, Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hM0 : 0 < l₀.M := by have := l₀.three_le; omega
  have hdM : l₁.M / l₀.M = 1 := by rw [hM]; exact Nat.div_self hM0
  have hdA : l₁.A / l₀.A = l₁.A := by rw [hA0, Nat.div_one]
  rw [LevComp, hdM, hdA] at hlev

  have hA0one : ∀ a, (Xo l₀).univ.etaA a = (Xo l₀).univ.eta 0 := by
    intro a
    have e := (Xo l₀).univ.etaA_ker a
    rw [hA0, one_smul] at e
    rw [e, eta_zero]

  have hgmem : ∀ x, g x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro x hx
    apply mem_of_eta_eq_one (Xo l₀).univ
    have e1 : (Xo l₀).univ.eta (g x) = (Xo l₀).univ.eta (g 0) := by
      rw [map_zero, eta_zero]
      exact (Xo l₀).univ.eta_ker _ hx
    have e2 : r₀.hom ≫ ((Xo l₀).univ.eta x).left = r₀.hom ≫ ((Xo l₀).univ.eta 0).left := by
      rw [← hg x, ← hg 0, e1]
    rw [← eta_zero (Xo l₀).univ]
    exact Over.OverMorphism.ext ((cancel_epi r₀.hom).1 e2)
  have hcop' : l₁.A.Coprime l₀.M := by rw [← hM]; exact hcop
  obtain ⟨ω, hωM, hωA, hων⟩ := hS E H D l₀ l₁.A g hpq l₁.A_pos hcop' hgmem
  obtain ⟨ρ, hρs, ν₁, hρe, hρA⟩ := exists_levAut (Xo l₁) hpq ω hων
  obtain ⟨o', m0, he, heA⟩ := GlobalTheory.exists_obj_twist_by_similitude GlobalTheory.SimAlg.sim_group E H D l₁ _ (baseKA l₁)
    (Xo l₁).X (Xo l₁).s (Xo l₁).univ ω hpq hων
  obtain ⟨m1, -, hinv'⟩ := exists_inverse_sabMap_id m0
  obtain ⟨a1, ha1⟩ := GlobalTheory.ObjMaps.exists_sab_comp ν ν₁
  obtain ⟨b1, hb1⟩ := GlobalTheory.ObjMaps.exists_sab_comp a1 m0
  obtain ⟨c1, hc1⟩ := exists_sabMap_phi_eq_of_eq (Category.id_comp _) b1
  obtain ⟨a2, ha2⟩ := GlobalTheory.ObjMaps.exists_sab_comp ν₀ ν
  obtain ⟨b2, hb2⟩ := GlobalTheory.ObjMaps.exists_sab_comp a2 m0
  obtain ⟨c2, hc2⟩ := exists_sabMap_phi_eq_of_eq (Category.id_comp _) b2
  have hρA0 := hρA 0
  rw [map_zero] at hρA0
  have heA0 := heA 0
  rw [map_zero] at heA0
  have hpw1 := etaA_pow_A' (Xo l₁).univ 0
  have hs12 : (ρ.hom ≫ r) ≫ (Xo l₀).s = (r ≫ r₀.hom) ≫ (Xo l₀).s := by
    rw [Category.assoc, Category.assoc, hr₀, hks, ← Category.assoc, hρs]
  have lev1 : LevComp o' (Xo l₀).univ (ρ.hom ≫ r) c1 := by
    rw [LevComp, hdM, hdA]
    refine ⟨fun a => ?_, fun a => ?_⟩
    · calc (o'.eta a ^ 1).left ≫ c1.φ
          = ((o'.eta a).left ≫ m0.φ) ≫ ν₁.φ ≫ ν.φ := by rw [hc1, hb1, ha1, _root_.pow_one, Category.assoc]
        _ = ρ.hom ≫ ((Xo l₁).univ.eta a ^ 1).left ≫ ν.φ := by
          rw [he a, ← Category.assoc, hρe a, Category.assoc, _root_.pow_one]
        _ = (ρ.hom ≫ r) ≫ ((Xo l₀).univ.eta a).left := by rw [hlev.1 a, Category.assoc]
    · calc (o'.etaA a ^ l₁.A).left ≫ c1.φ
          = ((o'.etaA 0).left ≫ m0.φ) ≫ ν₁.φ ≫ ν.φ := by
            rw [hc1, hb1, ha1, etaA_pow_A', Category.assoc]
        _ = ρ.hom ≫ ((Xo l₁).univ.etaA 0 ^ l₁.A).left ≫ ν.φ := by
          rw [heA0, ← Category.assoc, hρA0, Category.assoc, hpw1]
        _ = (ρ.hom ≫ r) ≫ ((Xo l₀).univ.etaA a).left := by
          rw [hlev.2 0, hA0one, hA0one, Category.assoc]
  have lev2 : LevComp o' (Xo l₀).univ (r ≫ r₀.hom) c2 := by
    rw [LevComp, hdM, hdA]
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have hmem : ω.f l₁.M a - g a ∈ l₁.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
        rw [hM, hMb]; exact hωM a
      calc (o'.eta a ^ 1).left ≫ c2.φ
          = ((o'.eta a).left ≫ m0.φ) ≫ ν.φ ≫ ν₀.φ := by rw [hc2, hb2, ha2, _root_.pow_one, Category.assoc]
        _ = ((Xo l₁).univ.eta (g a) ^ 1).left ≫ ν.φ ≫ ν₀.φ := by
          rw [he a, eta_congr (Xo l₁).univ hmem, _root_.pow_one]
        _ = (r ≫ r₀.hom) ≫ ((Xo l₀).univ.eta a).left := by
          rw [← Category.assoc, hlev.1 (g a), Category.assoc, hg a, Category.assoc]
    · calc (o'.etaA a ^ l₁.A).left ≫ c2.φ
          = ((o'.etaA 0).left ≫ m0.φ) ≫ ν.φ ≫ ν₀.φ := by
            rw [hc2, hb2, ha2, etaA_pow_A', Category.assoc]
        _ = (((Xo l₁).univ.etaA 0 ^ l₁.A).left ≫ ν.φ) ≫ ν₀.φ := by
          rw [heA0, hpw1, Category.assoc]
        _ = r ≫ ((Xo l₀).univ.eta (g 0)).left ≫ ν₀.φ := by
          rw [hlev.2 0, hA0one, map_zero, Category.assoc]
        _ = (r ≫ r₀.hom) ≫ ((Xo l₀).univ.etaA a).left := by
          rw [hg 0, hA0one, Category.assoc]
  obtain ⟨hr, hφ⟩ := hU hL1 hL2 hL3 E H D l₀ l₁ (Xo l₀) _ (baseKA l₁) (Xo l₁).X (Xo l₁).s o' _ _ c1 c2
    (hred l₁) hs12 lev1 lev2
  have hφ' : ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ := by
    calc ν₁.φ ≫ ν.φ = (m1.φ ≫ m0.φ) ≫ ν₁.φ ≫ ν.φ := by rw [hinv', Category.id_comp]
      _ = m1.φ ≫ c1.φ := by rw [hc1, hb1, ha1, Category.assoc]
      _ = m1.φ ≫ c2.φ := by rw [hφ]
      _ = ν.φ ≫ ν₀.φ := by rw [hc2, hb2, ha2, ← Category.assoc, hinv', Category.id_comp]
  refine ⟨ρ, ν₁, hρs, hr, hφ', fun x => ?_⟩
  have e := hρA x
  rwa [etaA_congr (Xo l₁).univ (hωA x)] at e

end GlobalTheory.LiftAut

end
