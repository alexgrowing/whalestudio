import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQpStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.PdEx

variable {l : ℕ} [Fact l.Prime]

def actOf {G k B : Type} [Group G] [CommRing k] [CommRing B] [Algebra k B] (s : G → B →+* B)
    (hmul : ∀ g h x, s (g * h) x = s g (s h x)) (hone : ∀ x, s 1 x = x)
    (hk : ∀ g c, s g (algebraMap k B c) = algebraMap k B c) : G →* (B ≃ₐ[k] B) where
  toFun g :=
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun x => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := map_mul (s g)
      map_add' := map_add (s g)
      commutes' := hk g }
  map_one' := AlgEquiv.ext fun x => hone x
  map_mul' g h := AlgEquiv.ext fun x => hmul g h x

def inc (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)

theorem inc_coe (K : FinExt l) (x : ↥(K0 K)) : ((inc K x : ↥(MaximalUnramifiedExtension l)) : Om l) = (x : Om l) := rfl

def sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (h : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) :=
  (((MaximalUnramifiedExtension l).val.comp σ).comp (inc K)).codRestrict (K0 K).toSubalgebra fun x =>
    ⟨h (inc K x) x.2.1, (σ (inc K x)).2⟩

theorem inc_sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (h) (x : ↥(K0 K)) :
    inc K (sigK K σ h x) = σ (inc K x) := Subtype.ext rfl

theorem finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

theorem fix (K : FinExt l) (g : ↥(GK K)) (x : Om l) (hx : x ∈ K.1) : (g : GQ l) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).1 g.2 x hx

theorem exists_abstract (R : LocRings l) (K : FinExt l)
    (sB : GQ l → R.B →+* R.B) (sD : GQ l → R.BdR →+* R.BdR) (φ : R.B →+* R.B) (ι : R.B →+* R.BdR)
    (F : ℤ → AddSubgroup R.BdR) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (χ : GQ l →* ℤ_[l]ˣ) (t : R.B)
    (hσ : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1)
    (sB_mul : ∀ g h x, sB (g * h) x = sB g (sB h x)) (sB_one : ∀ x, sB 1 x = x)
    (sD_mul : ∀ g h x, sD (g * h) x = sD g (sD h x)) (sD_one : ∀ x, sD 1 x = x)
    (sB_u : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
      sB g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c')
    (sD_o : ∀ (g : GQ l) (x : Om l), sD g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x))
    (invB : ∀ b, (∀ g ∈ GK K, sB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ algebraMap ↥(MaximalUnramifiedExtension l) R.B c = b)
    (invD : ∀ b, (∀ g ∈ GK K, sD g b = b) → ∃ y ∈ K.1, algebraMap (Om l) R.BdR y = b)
    (φ_inj : Function.Injective φ)
    (φ_u : ∀ c, φ (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B (σ c))
    (φ_comm : ∀ g b, φ (sB g b) = sB g (φ b))
    (ι_u : ∀ c : ↥(MaximalUnramifiedExtension l), ι (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap (Om l) R.BdR (c : Om l))
    (ι_inj : Function.Injective ι) (ι_comm : ∀ g b, ι (sB g b) = sD g (ι b))
    (F_o : ∀ x : Om l, algebraMap (Om l) R.BdR x ∈ F 0)
    (F_anti : ∀ a, F (a + 1) ≤ F a)
    (F_mul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (F_exh : ∀ x, ∃ a, x ∈ F a) (F_sep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (F_G : ∀ g a x, x ∈ F a → sD g x ∈ F a)
    (t_unit : IsUnit t)
    (t_act : ∀ g, sB g t = algebraMap ℚ_[l] R.B ((χ g : ℤ_[l]) : ℚ_[l]) * t)
    (t_φ : φ t = (l : R.B) * t) (t1 : ι t ∈ F 1) (t2 : ι t ∉ F 2)
    (fund : ∀ b, φ b = b → ι b ∈ F 0 → ∃ c : ℚ_[l], algebraMap ℚ_[l] R.B c = b) :
    ∃ PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR,
      PD.p = l ∧ (∀ g b, PD.actB g b = sB g b) ∧ (∀ g b, PD.actdR g b = sD g b) ∧ (∀ b, PD.φ b = φ b) ∧
      (∀ b, PD.ι b = ι b) ∧ PD.t = t ∧ (∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ (g : GQ l) : ℤ_[l]) : ℚ_[l])) ∧
      (∀ a x, x ∈ PD.Fil a ↔ x ∈ F a) ∧
      ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
        ((PD.σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have aB : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (inc K c) := fun _ => rfl
  have aD : ∀ c : ↥K.1, algebraMap ↥K.1 R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aD0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aQ : ∀ c : ℚ_[l], algebraMap ℚ_[l] R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) :=
    fun c => IsScalarTower.algebraMap_apply _ _ _ c
  haveI := finiteDimensional_maxUnramifiedSubfield K
  refine ⟨{
    p := l
    hp := Fact.out
    finK₀ := finiteDimensional_maxUnramifiedSubfield K
    finK := K.2
    σ := sigK K σ hσ
    σ_bij := AlgHom.bijective _
    actB := actOf (fun g : ↥(GK K) => sB g) (fun g h x => sB_mul g h x) (fun x => sB_one x)
      (fun g c => by rw [aB]; exact sB_u g _ _ (fix K g _ c.2.1))
    invB := fun b hb => by
      obtain ⟨c, hc, e⟩ := invB b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc, c.2⟩, e⟩
    φ := AlgHom.mk φ fun c => by
      change φ _ = _
      rw [aQ, φ_u, AlgHom.commutes]
    φ_inj := φ_inj
    φ_K₀ := fun c => by
      change φ _ = _
      rw [aB, aB, φ_u, inc_sigK]
    φ_comm := fun g b => φ_comm g b
    actdR := actOf (fun g : ↥(GK K) => sD g) (fun g h x => sD_mul g h x) (fun x => sD_one x)
      (fun g c => by rw [aD, sD_o, fix K g _ c.2])
    invdR := fun b hb => by
      obtain ⟨c, hc, e⟩ := invD b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc⟩, e⟩
    ι := AlgHom.mk ι fun c => by
      change ι _ = _
      rw [aB, aD0, ι_u, inc_coe]
    ι_inj := ι_inj
    ι_comm := fun g b => ι_comm g b
    Fil := fun a =>
      { carrier := F a
        add_mem' := fun hx hy => (F a).add_mem hx hy
        zero_mem' := (F a).zero_mem
        smul_mem' := fun c x hx => by
          have := F_mul 0 a _ _ (F_o (c : Om l)) hx
          rw [zero_add, ← aD, ← Algebra.smul_def] at this
          exact this }
    Fil_anti := fun a x hx => F_anti a hx
    one_mem := by
      have := F_o 1
      rw [map_one] at this
      exact this
    Fil_mul := F_mul
    Fil_exh := F_exh
    Fil_sep := F_sep
    Fil_G := fun g a x hx => F_G g a x hx
    χ := ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp χ).comp (GK K).subtype
    t := t
    t_unit := t_unit
    t_act := fun g => by
      rw [Algebra.smul_def]
      exact t_act g
    t_φ := by
      rw [Algebra.smul_def, map_natCast]
      exact t_φ
    mem_filtration_one := t1
    not_mem_filtration_two := t2
    fund := fund }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ => Iff.rfl, fun x c h => ?_⟩
  have : inc K x = c := Subtype.ext h.symm
  rw [← this]
  rfl

theorem exists_realPD : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  intro l _ C K
  obtain ⟨a1, a2, a3, a4, a5, -, -, -, -, a10, -, a12, a13⟩ := ActLaws.act_laws l
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.bdR_filtration_laws l
  obtain ⟨u1, u2, -, u4, u5, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have hσ := (frob_laws l C.σ C.σ_root).2.1 K
  have so := (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2
  have sD_o : ∀ (g : GQ l) (x : Om l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) (C.o x)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (g x)) := fun g x => by rw [a10, so]
  have F_o : ∀ x : Om l, algebraMap (Per.BdRp l) (Per.BdR l) (C.o x) ∈ Per.FilD l 0 := fun x => by
    have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (f7 0 1).1 (by rw [map_one]; exact f2)
    have h2 : C.o x * 1 ∈ Per.FilP l 0 := Ideal.mul_mem_left _ _ h1
    rw [mul_one] at h2
    exact (f7 0 _).2 h2
  have u_z : ∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) := fun z => by
    apply u4
    have e1 : ((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]) : ↥(MaximalUnramifiedExtension l)) : Om l) = algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) :=
      (IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) (Om l) (z : ℚ_[l])).symm
    rw [C.ι_u, C.ι_j, ULaws.alg_acris, C.j_cris.on0, e1, C.o_sec.z, Subalgebra.coe_algebraMap, aDp,
      RingHom.comp_apply]
  have t_act : ∀ g : GQ l, Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((C.χ g : ℤ_[l]) : ℚ_[l])) * algebraMap (Per.Acris l) (Per.Bcris l) C.t :=
    fun g => by
      rw [a12, GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C g, map_mul, u_z]
  have t_φ : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) C.t := by
    rw [a13, GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C, map_mul, map_natCast]
  have s1 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∈ Per.FilD l 1 := by
    rw [C.ι_j]
    exact (f7 1 _).2 t2
  have s2 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∉ Per.FilD l 2 := by
    rw [C.ι_j]
    exact fun h => t3 ((f7 2 _).1 h)
  obtain ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_abstract (ringsOf C) K
    (fun g => Per.σB g) (fun g => Per.σD g) (Per.φB l) C.ι (fun a => (Per.FilD l a).toAddSubgroup) C.σ C.χ
    (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hσ a1 a2 a3 a4 u2 sD_o
    (InvCris.invariants_Bcris l C K) (GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K) (GlobalTheory.T.frobenius_period_ring_injective l) u1 (fun g b => a5 g b) C.ι_u u4 u5
    F_o f1 f3 f4 f5 f6 t1 t_act t_φ s1 s2 (GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C)
  exact ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end GlobalTheory.MemLoc.PdEx
