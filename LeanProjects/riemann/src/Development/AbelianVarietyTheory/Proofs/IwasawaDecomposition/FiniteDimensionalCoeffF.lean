import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LvCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def top (l₁ l₂ : Level H) : Level H :=
  { l₁ with
    A := l₁.A * l₁.M * l₂.M * l₂.A
    A_pos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos l₁.A_pos (by have := l₁.three_le; omega))
      (by have := l₂.three_le; omega)) l₂.A_pos }

def side (l₁ l₂ : Level H) : Level H := { l₂ with A := (top l₁ l₂).A, A_pos := (top l₁ l₂).A_pos }

theorem top_A (l₁ l₂ : Level H) : (top l₁ l₂).A = l₁.A * l₁.M * l₂.M * l₂.A := rfl

theorem side_A (l₁ l₂ : Level H) : (side l₁ l₂).A = (top l₁ l₂).A := rfl

theorem dvd_top (l₁ l₂ : Level H) : l₁.Dvd (top l₁ l₂) :=
  ⟨dvd_rfl, le_rfl, ⟨l₁.M * l₂.M * l₂.A, by rw [top_A]; ring⟩⟩

theorem dvd_side (l₁ l₂ : Level H) : l₂.Dvd (side l₁ l₂) :=
  ⟨dvd_rfl, le_rfl, ⟨l₁.A * l₁.M * l₂.M, by rw [side_A, top_A]; ring⟩⟩

theorem M_dvd_top (l₁ l₂ : Level H) : l₁.M ∣ (top l₁ l₂).A := ⟨l₁.A * l₂.M * l₂.A, by rw [top_A]; ring⟩

theorem M_dvd_side (l₁ l₂ : Level H) : l₂.M ∣ (side l₁ l₂).A := ⟨l₁.A * l₁.M * l₂.A, by rw [side_A, top_A]; ring⟩

end GlobalTheory.LvCover

namespace GlobalTheory.LvCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_integral {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (zeta n) :=
  IsIntegral.of_pow hn (by
    rw [show zeta n ^ n = 1 from (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one]
    exact isIntegral_one)

theorem M'_pos (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

def coeffF {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : IntermediateField ℚ ℂ :=
  c₁.F ⊔ c₂.F ⊔ IntermediateField.adjoin ℚ {zeta (top l₁ l₂).M'}

theorem finiteDimensional_coeffF {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) :
    FiniteDimensional ℚ (coeffF c₁ c₂) := by
  haveI := c₁.fin
  haveI := c₂.fin
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta (top l₁ l₂).M'}) :=
    IntermediateField.adjoin.finiteDimensional (zeta_integral (M'_pos _))
  unfold coeffF
  infer_instance

theorem zeta_mem_coeffF {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : zeta (top l₁ l₂).M' ∈ coeffF c₁ c₂ :=
  (le_sup_right : _ ≤ coeffF c₁ c₂) (IntermediateField.subset_adjoin _ _ rfl)

theorem le_coeffF₁ {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : c₁.F ≤ coeffF c₁ c₂ :=
  le_sup_left.trans le_sup_left

theorem le_coeffF₂ {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : c₂.F ≤ coeffF c₁ c₂ :=
  le_sup_right.trans le_sup_left

theorem KA_le_coeffF {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : KA (top l₁ l₂) ≤ coeffF c₁ c₂ := by
  rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨le_coeffF₁ c₁ c₂ (c₁.le (IntermediateField.subset_adjoin _ _ (by simp))), ?_⟩
  rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos _) (Nat.dvd_lcm_right _ _)]
  exact pow_mem (zeta_mem_coeffF c₁ c₂) _

def coeffTop {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : Coeff (top l₁ l₂) where
  F := coeffF c₁ c₂
  fin := finiteDimensional_coeffF c₁ c₂
  conj τ a := le_coeffF₁ c₁ c₂ (c₁.conj τ a)
  zeta_mem := zeta_mem_coeffF c₁ c₂
  le := KA_le_coeffF c₁ c₂

def coeffSide {l₁ l₂ : Level H} (c₁ : Coeff l₁) (c₂ : Coeff l₂) : Coeff (side l₁ l₂) where
  F := coeffF c₁ c₂
  fin := finiteDimensional_coeffF c₁ c₂
  conj τ a := le_coeffF₁ c₁ c₂ (c₁.conj τ a)
  zeta_mem := by
    have h : (side l₁ l₂).M' ∣ (top l₁ l₂).M' :=
      Nat.lcm_dvd ((M_dvd_side l₁ l₂).trans (Nat.dvd_lcm_right _ _)) (Nat.dvd_lcm_right _ _)
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos _) h]
    exact pow_mem (zeta_mem_coeffF c₁ c₂) _
  le := KA_le_coeffF c₁ c₂

def intMap {K L : IntermediateField ℚ ℂ} (h : K ≤ L) : 𝓞 K →+* 𝓞 L :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom

variable {D : Datum H}

def fieldMap {l : Level H} (Xo : Moduli D l) {c c' : Coeff l} (h : c.F ≤ c'.F) : Xo.XF c' ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion h).toRingHom) (by
    rw [pullback.condition, Category.assoc, GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp])

def GoodMap {l l' : Level H} {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} (h : c'.F ≤ c.F)
    (Y : GlobalTheory.TorRef.GMod Xo c) (Y' : GlobalTheory.TorRef.GMod Xo' c') (r : Xo.XF c ⟶ Xo'.XF c') : Prop :=
  Nonempty (GlobalTheory.ShFam.TwMap (RingEquiv.refl (𝓞 E)) Y.oF.t Y'.oF.t r) ∧ Function.Surjective r ∧
    r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion h).toRingHom

end GlobalTheory.LvCover

namespace GlobalTheory.LvCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_split (l : Level H) :
    ∃ u ∈ l.Mb, ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), u + v = 1 :=
  Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) from l.coprime ▸ Submodule.mem_top)

def uOf (l : Level H) : 𝓞 E := (exists_split l).choose

def vOf (l : Level H) : 𝓞 E := (exists_split l).choose_spec.2.choose

theorem uOf_mem (l : Level H) : uOf l ∈ l.Mb := (exists_split l).choose_spec.1

theorem vOf_mem (l : Level H) : vOf l ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) :=
  (exists_split l).choose_spec.2.choose_spec.1

theorem uOf_add_vOf (l : Level H) : uOf l + vOf l = 1 := (exists_split l).choose_spec.2.choose_spec.2

variable {D : Datum H}

theorem smul_eq_nsmul_of_mem {I J : Ideal (𝓞 E)} {M : ℕ} (hIJ : ∀ x ∈ I, ∀ y ∈ J, ∃ q : 𝓞 E, x * y = M * q)
    {x : 𝓞 E} (hx : x ∈ I) {a : D.La} (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : ∃ b : D.La, x • a = M • b := by
  refine Submodule.smul_induction_on ha (fun r hr m _ => ?_) (fun y z hy hz => ?_)
  · obtain ⟨q, hq⟩ := hIJ x hx r hr
    exact ⟨q • m, by rw [smul_smul, hq, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · obtain ⟨b, hb⟩ := hy
    obtain ⟨b', hb'⟩ := hz
    exact ⟨b + b', by rw [smul_add, hb, hb', smul_add]⟩

theorem mul_mem_M (l : Level H) {x y : 𝓞 E} (hx : x ∈ l.Mb) (hy : y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :
    ∃ q : 𝓞 E, x * y = l.M * q := by
  have := l.prod ▸ Ideal.mul_mem_mul hx hy
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨q, by rw [← hq, mul_comm]⟩

def reM {l l' : Level H} {B : Type} [CommRing B] {b : Base l B} {b' : Base l' B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) (hM : l'.M ∣ l.A) (hA : l'.A ∣ l.A) (hρ : b'.ρ = b.ρ) (hζ : b'.ζ = b.ζ ^ (l.A / l'.A)) :
    Obj D l' b' s where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.etaA ((l.A / l'.M) • (vOf l' • a))
  eta_add a c := by rw [smul_add, smul_add, o.etaA_add]
  eta_ker a ha := by
    obtain ⟨q, hq⟩ := smul_eq_nsmul_of_mem (I := l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (J := l'.Mb)
      (fun x hx y hy => by rw [mul_comm]; exact mul_mem_M l' hy hx) (vOf_mem l') ha
    rw [hq, smul_smul, Nat.div_mul_cancel hM, o.etaA_ker]
  etaA a := o.etaA ((l.A / l'.A) • a)
  etaA_add a c := by rw [smul_add, o.etaA_add]
  etaA_ker a := by rw [smul_smul, Nat.div_mul_cancel hA, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, h₁, h₂, -⟩ := o.geom k x β hx
    have hq : 0 < l.A / l'.A := Nat.div_pos (Nat.le_of_dvd l.A_pos hA) l'.A_pos
    have hM' : 0 < l'.M := by have := l'.three_le; omega
    have hqM : 0 < l.A / l'.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hM) hM'
    refine ⟨hρ ▸ hd, I, ?_, fun a => ?_, fun a ha => ?_⟩
    · rw [hζ, map_pow, ← h₁, ← I.ζ_pow l'.A _ l'.A_pos hq, Nat.mul_div_cancel' hA, Units.val_pow_eq_pow_val]
    · rw [h₂, GlobalTheory.ObjLower.map_nsmul_of_add _ (I.add _), ← I.tower l'.A _ l'.A_pos hq, Nat.mul_div_cancel' hA]
    · obtain ⟨q, hq'⟩ := smul_eq_nsmul_of_mem (I := l'.Mb) (J := l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
        (fun x hx y hy => mul_mem_M l' hx hy) (uOf_mem l') ha
      have e : a = uOf l' • a + vOf l' • a := by rw [← add_smul, uOf_add_vOf, one_smul]
      have key : I.ev l'.M a = I.ev l'.M (vOf l' • a) := by
        conv_lhs => rw [e]
        rw [I.add, hq', (I.ker l'.M hM' _).2 ⟨q, rfl⟩, _root_.one_mul]
      rw [h₂, GlobalTheory.ObjLower.map_nsmul_of_add _ (I.add _), key, ← I.tower l'.M _ hM' hqM, Nat.mul_div_cancel' hM]

def reMap {l l' : Level H} {B B₀ : Type} [CommRing B] [CommRing B₀] {b : Base l B} {b' : Base l' B} {b₀ : Base l B₀}
    {b₀' : Base l' B₀} {S S₀ : Scheme.{0}} {s : S ⟶ Sp B} {s₀ : S₀ ⟶ Sp B₀} {o : Obj D l b s} {o₀ : Obj D l b₀ s₀}
    {f : S ⟶ S₀} (m : ObjMap o o₀ f) (hM : l'.M ∣ l.A) (hA : l'.A ∣ l.A) (hρ : b'.ρ = b.ρ)
    (hζ : b'.ζ = b.ζ ^ (l.A / l'.A)) (hρ₀ : b₀'.ρ = b₀.ρ) (hζ₀ : b₀'.ζ = b₀.ζ ^ (l.A / l'.A)) :
    ObjMap (reM o hM hA hρ hζ) (reM o₀ hM hA hρ₀ hζ₀) f where
  toSABMap := m.toSABMap
  eta a := m.etaA ((l.A / l'.M) • (vOf l' • a))
  etaA a := m.etaA ((l.A / l'.A) • a)

end GlobalTheory.LvCover

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LvCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem intMap_finite {K L : IntermediateField ℚ ℂ} (h : K ≤ L) [FiniteDimensional ℚ L] : (intMap h).Finite := by
  haveI : NumberField L := {}
  letI := (intMap h).toAlgebra
  show Module.Finite (𝓞 K) (𝓞 L)
  exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)

theorem j_s_eq {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : GMod Xo c) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem j_s_of_snd {l l' : Level H} {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} (h : c'.F ≤ c.F)
    (Y : GMod Xo c) (Y' : GMod Xo' c') (r : Xo.XF c ⟶ Xo'.XF c')
    (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion h).toRingHom) :
    r ≫ Y'.j ≫ Y'.s = Y.j ≫ Y.s ≫ spMap (intMap h) := by
  rw [j_s_eq Y', ← Category.assoc, hr, ← Category.assoc Y.j Y.s, j_s_eq Y, Category.assoc, Category.assoc,
    GlobalTheory.Models.RankZero.spMap_comp, GlobalTheory.Models.RankZero.spMap_comp]
  congr 2

theorem GoodMap.comp {l l' l'' : Level H} {Xo : Moduli D l} {Xo' : Moduli D l'} {Xo'' : Moduli D l''} {c : Coeff l}
    {c' : Coeff l'} {c'' : Coeff l''} {h : c'.F ≤ c.F} {h' : c''.F ≤ c'.F} {Y : GMod Xo c} {Y' : GMod Xo' c'}
    {Y'' : GMod Xo'' c''} {r : Xo.XF c ⟶ Xo'.XF c'} {r' : Xo'.XF c' ⟶ Xo''.XF c''} (hr : GoodMap h Y Y' r)
    (hr' : GoodMap h' Y' Y'' r') : GoodMap (h'.trans h) Y Y'' (r ≫ r') := by
  obtain ⟨⟨m⟩, s, e⟩ := hr
  obtain ⟨⟨m'⟩, s', e'⟩ := hr'
  obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp (GlobalTheory.ShFam.TwMap.reflEquiv _ _ _ m)
    (GlobalTheory.ShFam.TwMap.reflEquiv _ _ _ m') rfl
  refine ⟨⟨(GlobalTheory.ShFam.TwMap.reflEquiv _ _ _).symm n⟩, fun z => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := s' z
    obtain ⟨x, rfl⟩ := s y
    exact ⟨x, rfl⟩
  · rw [Category.assoc, e', ← Category.assoc, e, Category.assoc, GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]

end GlobalTheory.LvCover
