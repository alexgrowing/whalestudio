import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCP
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab

variable {D : D7}

structure ChrIn (D : D7) where
  chr : D.what₂.Tup → ℕ → chrA D
  chr_exp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)).1 τ (-(D.hc τ).e j)
  chr_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j).1 0
  eta : chrA D
  eta_exp : ∀ τ, HasInfExp D eta.1 τ (1 / 2)
  eta_res : ResEta D eta.1 1
  eta_unr : UnramEverywhere D eta.1

abbrev lowY (D : D7) (t j i : ℕ) : HSp D := lowC ((towC D t).Ys j) i

structure Free {ψ : AddChar (AF D.host.F) ℂ} (_Om : WeilC ψ) : Type 1 where
  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V
  fact : ∀ V W, Set (schC ψ V W)
  conjS : ∀ V W, schC ψ V W → schC ψ V W
  conjS_add : ∀ V W Φ Φ', conjS V W (Φ + Φ') = conjS V W Φ + conjS V W Φ'
  conjS_smul : ∀ V W (c : ℂ) Φ, conjS V W (c • Φ) = star c • conjS V W Φ
  conjS_conjS : ∀ V W Φ, conjS V W (conjS V W Φ) = Φ
  conjS_fact : ∀ V W, ∀ Φ ∈ fact V W, conjS V W Φ ∈ fact V W
  conjS_kfin : ∀ V W, ∀ Φ ∈ kfinC ψ V W, conjS V W Φ ∈ kfinC ψ V W

  PosE : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  FJd : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  [fjAdd : ∀ A B ι, AddCommGroup (FJd A B ι)]
  [fjMod : ∀ A B ι, Module ℂ (FJd A B ι)]
  BE : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), PosE A B ι → FJd A B ι → afC D A → cuspC D B → ℂ
  BE_right : ∀ A B ι p s φ, IsLinearMap ℂ (BE A B ι p s φ)
  BE_add : ∀ A B ι p s φ φ' F, BE A B ι p s (φ + φ') F = BE A B ι p s φ F + BE A B ι p s φ' F
  BE_smul : ∀ A B ι p s (c : ℂ) φ F, BE A B ι p s (c • φ) F = star c * BE A B ι p s φ F
  pos1 : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}
  posSym : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}

  f1 : ∀ u, Matrix (Fin (D.sp.Y 0).rank) (Fin (pos1 u).1.ρ) D.host.E
  free_flag_dual : ∀ u, IsDualFlag (pos1 u).1 (f1 u)
  colAF : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] cuspC D (D.sp.X j)
  PhiX : ∀ (_u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.X j) (D.sp.X (j + 1))
  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cuspC D (D.sp.Y j)
  PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.Y (j + 1)) (D.sp.Y j)
  PhiYLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y (j + 1)) (lowY D D.R.t j i)
  PhiYupLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y j) (lowY D D.R.t (j + 1) i)
  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j
  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1
  mY_zero : ∀ μ, mY μ 0 = 1

attribute [instance] Free.fjAdd Free.fjMod

variable {ψ : AddChar (AF D.host.F) ℂ}

def PosC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  {d : BesDat A B ι // (d.y : GA D B) = 1} ⊕ {_p : f.PosE A B ι // ¬ Odd (B.rank - A.rank)}

def bperC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) :
    PosC f A B ι → f.FJd A B ι → afC D A → cuspC D B → ℂ
  | Sum.inl d => fun _ => besC ψ f.petF d.1
  | Sum.inr p => f.BE A B ι p.1

def datC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (h : Odd (B.rank - A.rank)) :
    PosC f A B ι → BesDat A B ι
  | Sum.inl d => d.1
  | Sum.inr p => absurd h p.2

def thetaOf (D : D7) {ψ : AddChar (AF D.host.F) ℂ} (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D)
    (f : Free Om) : ThetaX D where
  AF := fun V => afC D V
  cusp := cuspC D
  pet := petC f.petF
  pet_add_left := fun V F F' H => by
    unfold petC intC
    rw [← mul_add, ← integral_add (pet_int G.volEx G.add G.cuspInt G.petInt V F H)
      (pet_int G.volEx G.add G.cuspInt G.petInt V F' H)]
    simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  pet_smul_left := fun V a F H => by
    unfold petC intC
    rw [mul_left_comm, ← integral_const_mul (star a)]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  pet_right := fun V F => ⟨fun H H' => by
      unfold petC intC
      rw [← mul_add, ← integral_add (pet_int G.volEx G.add G.cuspInt G.petInt V F H)
        (pet_int G.volEx G.add G.cuspInt G.petInt V F H')]
      simp only [Submodule.coe_add, Pi.add_apply, mul_add], fun a H => by
      unfold petC intC
      rw [smul_eq_mul, mul_left_comm, ← integral_const_mul a]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm a]⟩
  pet_symm := fun V F H => by
    unfold petC intC
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← integral_conj]
    simp only [map_mul, Complex.conj_conj, mul_comm]
  pet_pos := petC_pos G.volEx G.add G.cuspInt G.petInt f.petF f.petF_pos
  actR := actRC G.right
  actR_one := fun V τ => by
    ext F x
    unfold actRC
    rw [actC_apply, atTau_one G.atTau, mul_one]
    rfl
  actR_mul := fun V τ g hg h hh => by
    ext F x
    unfold actRC
    rw [Module.End.mul_apply, actC_apply, actC_apply, actC_apply, atTau_mul G.atTau V τ hg hh, mul_assoc]
  actR_cusp := fun V τ g _ => actC_cusp G.right V _ _
  Gf := fun V => GfC V
  actF := actFC G.right
  actF_cusp := fun V g => actC_cusp G.right V _ (Or.inl g.2)
  actF_actR := fun V g τ h => by
    ext F x
    show F.1 (x * (g : GA D V) * atTau (th0 D) V τ h) = F.1 (x * atTau (th0 D) V τ h * (g : GA D V))
    rw [mul_assoc, mul_assoc, fin_inf_comm g.2 (atTau_mem _ V τ h)]
  Ksph := ksphC
  Ksph_mono := fun V S S' hS g hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩
  typ := typC D
  Chr := chrA D
  infTy := infTyC
  infTy_mul := fun χ χ' τ => hE _ τ _ _ (infTyC_spec (χ * χ') τ) (hasInfExp_mul (infTyC_spec χ τ) (infTyC_spec χ' τ))
  chrOf := c.chr
  chrOf_inf := fun μ j τ => hE _ τ _ _ (infTyC_spec _ τ) (c.chr_exp μ j τ)
  etaT := c.eta
  etaT_inf := fun τ => Or.inl (hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ))
  etaT_pos := fun τ => hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ)
  Sch := fun V W => schC ψ V W
  fact := f.fact
  kfin := kfinC ψ
  th := thC G Om f.petF
  Xs := fun t => (towC D t).Xs
  Xs_rank := fun t => (towC D t).Xs_rank
  Xs_sig := fun t => (towC D t).Xs_sig
  Ys := fun t => (towC D t).Ys
  Ys_rank := fun t => (towC D t).Ys_rank
  Ys_sig := fun t => (towC D t).Ys_sig
  iXYs := fun t => (towC D t).iXYs
  iXYs_isom := fun t => (towC D t).iXYs_isom
  iYXm := fun t => (towC D t).iYXm
  iYXm_isom := fun t => (towC D t).iYXm_isom
  YsLow := lowY D
  YsLow_zero := fun _ _ => if_pos rfl
  Xs_rec := fun j _ => by rw [towC_rec]; rfl
  Ys_rec := fun j _ => by rw [towC_rec]; rfl
  conjAF := conjC G.conj
  conjAF_add := conjC_add G.conj
  conjAF_smul := conjC_smul G.conj
  conjAF_conjAF := fun _ _ => Subtype.ext (star_star _)
  conjAF_cusp := conjC_cusp G.conj
  Pos := PosC f
  FJd := f.FJd
  Bper := bperC f
  Bper_right := fun A B ι p s φ => by
    rcases p with d | p
    · exact besC_right G P f.petF d.1 φ
    · exact f.BE_right A B ι p.1 s φ
  Bper_add_left := fun A B ι p s φ φ' F => by
    rcases p with d | p
    · exact besC_add G P f.petF d.1 φ φ' F
    · exact f.BE_add A B ι p.1 s φ φ' F
  Bper_smul_left := fun A B ι p s a φ F => by
    rcases p with d | p
    · exact besC_smul f.petF d.1 a φ F
    · exact f.BE_smul A B ι p.1 s a φ F
  Bper_odd := fun A B ι p h s s' φ F => by
    rcases p with d | p
    · rfl
    · exact absurd h p.2
  Btop := btopC f.petF
  Btop_right := btopC_right G P.topInt f.petF
  Btop_add_left := btopC_add G P.topInt f.petF
  Btop_smul_left := pairing_smul_left₂ f.petF
  pos1 := fun u => Sum.inl (f.pos1 u)
  posSym := fun u => Sum.inl (f.posSym u)
  colAF := f.colAF
  rowAF := f.rowAF
  PhiY := f.PhiY
  PhiYup := fun μ j => swapC ψ _ _ (f.PhiY μ j)
  mY := f.mY
  mY_pos := f.mY_pos
  adelicDataRowMeasureScale_trivialTuple := f.adelicDataRowMeasureScale_trivialTuple
  mY_zero := f.mY_zero

section Ties

variable (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D) (f : Free Om)

def thetaCompatibilityOf (hS : SpSig D) (hW : WittLow D) : ThetaTied D (thetaOf D G P hE Om c f) where
  ev := fun V => (afC D V).subtype
  ev_inj := fun V => (afC D V).injective_subtype
  ev_aut := fun V F => ((mem_afC G.add).1 F.2).toIsAutFun
  cusp := fun V F => mem_cuspC G.add G.cuspInt
  eGf := fun V => MulEquiv.refl _
  actF := fun _ _ _ _ => rfl
  actR := allSome_fam.2 fun V τ g hg => ⟨(G.atTau V τ g hg).exists, fun h hh F x => by
    rw [← atTau_eq G.atTau hg hh]; rfl⟩
  ksph := fun _ _ _ => Iff.rfl
  conj := fun _ _ _ => rfl
  petF := f.petF
  petF_pos := f.petF_pos
  petR := petRC D
  petR_pos := petRC_pos
  petR_def := fun N => ⟨if_pos (Or.inr rfl), if_pos (Or.inl rfl)⟩
  petR_minf := petRC_minf
  pet := fun V hV μ 𝓕 hp F H => by
    show petC f.petF V F H = _
    unfold petC
    rw [intC_eq G.volEx G.volU hV hp]
    · rfl
    · intro γ hγ x
      rw [((mem_afC G.add).1 F.2).left γ hγ, ((mem_afC G.add).1 H.1.2).left γ hγ]
  btop := fun A B ι hB hι μ 𝓕 hp s hs φ F => btopC_eq G P.embU P.embRat f.petF A B ι hB hι μ 𝓕 hp s hs φ F
  eChr := (chrA D).subtype
  eChr_inj := (chrA D).subtype_injective
  eChr_range := Subtype.range_coe
  infTy := infTyC_spec
  chrOf_res := c.chr_res
  etaT_res := c.eta_res
  etaT_unr := c.eta_unr
  etaT_exp := fun τ => hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ)
  xs_pos := fun t j hj => (towC_sig hS t j hj).1
  ys_sig := fun t j hj => (towC_sig hS t j hj).2
  ysLow := fun t j i h => lowC_spec hW _ (towC_ok t j) i h

def weilCompatibilityOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    WeilTied D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) where
  ψ := ψ
  ψ_std := hψ
  evS := fun V W => (schC ψ V W).subtype
  evS_inj := fun V W => (schC ψ V W).injective_subtype
  evS_range := fun V W _ => Subtype.range_coe
  om := Om.om
  om_heis := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).Heisenberg₂
  om_aut := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).aut
  om_cont := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).cont
  om_unit := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).unit
  om_split := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).split
  om_tw := ⟨fun V W χ χ' ν h => Om.twW_up V W χ χ' ν h.le, fun V W χ χ' ν h => Om.twV_up V W χ χ' ν h.le, Om.twW_dn, Om.twV_dn⟩
  om_swap := fun V W χ χ' a b d => Om.swap V W χ χ' a ⟨b, d⟩
  th := fun V W χ χ' _ b d hV μ 𝓕 hp Φ F h => thC_apply G Om f.petF ⟨b, d⟩ hV hp Φ F h

theorem weilTiedEqOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    WeilCompatibleEquivariance (weilCompatibilityOf G P hE Om c f hS hW hψ) where
  evS_range := fun _ _ _ => Subtype.range_coe
  om_heis := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).Heisenberg₂
  om_aut := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).aut
  om_cont := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).cont
  om_unit := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).unit
  om_split := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).split
  om_tw := ⟨fun V W χ χ' ν h => Om.twW_up V W χ χ' ν h.le, fun V W χ χ' ν h => Om.twV_up V W χ χ' ν h.le⟩
  th := fun V W χ χ' _ b d hV μ 𝓕 hp Φ F h => thC_apply G Om f.petF ⟨b, d⟩ hV hp Φ F h

theorem besselUnipotentSubgroup_zero_subsingleton {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f0 : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Subsingleton (besselUnipotentSubgroup d f0 0) := by
  have h : besselUnipotentSubgroup d f0 0 = ⊥ := by
    unfold besselUnipotentSubgroup
    rw [Subgroup.closure_eq_bot_iff]
    rintro g ⟨hg, -⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := hg i j
    rw [RingHom.map_zero, add_zero, zero_mul] at this
    have e : (mt B g - 1) i j = 0 := this.symm
    rw [Matrix.sub_apply, sub_eq_zero] at e
    exact e
  rw [h]
  infer_instance

theorem dirac_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (_ : Subsingleton G) :
    (Measure.dirac (1 : G)).IsHaarMeasure :=
  { toIsMulLeftInvariant := ⟨fun g => by rw [@Subsingleton.elim _ ‹Subsingleton G› g 1]; simp [Measure.map_id']⟩
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsOpenPosMeasure := ⟨fun U _ hne => by
      obtain ⟨x, hx⟩ := hne
      rw [@Subsingleton.elim _ ‹Subsingleton G› x 1] at hx
      rw [Measure.dirac_apply_of_mem hx]
      exact one_ne_zero⟩ }

theorem integral_dirac_one_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] (hs : Subsingleton G) (g : G → ℂ) :
    ∫ x, g x ∂(Measure.dirac (1 : G)) = g 1 := by
  rw [show g = fun _ => g 1 from funext fun x => by rw [@Subsingleton.elim _ hs x 1], integral_const]
  simp

def besselOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    BesselTied D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) (weilCompatibilityOf G P hE Om c f hS hW hψ) where
  dat := datC f
  dat_y := fun A B ι h p => by
    rcases p with d | p
    · exact d.2
    · exact absurd h p.2
  besC := fun _ _ _ _ => 1
  besC_pos := fun _ _ _ _ => one_pos
  bper := fun A B ι ho _ hA hι p hn sF μ 𝓕 hp μN 𝓕N n1 n2 n3 s hs φ F hφ => by
    rcases p with d | p
    · rw [one_mul]
      exact besC_eq G P f.petF d.1 hA hι μ 𝓕 hp (μN, 𝓕N) ⟨n1, n2, n3⟩ s hs φ F hφ
    · exact absurd ho p.2
  besC_one := fun _ _ _ _ => rfl

def b1Of (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    BesselCompatibility' D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) (weilCompatibilityOf G P hE Om c f hS hW hψ)
      (besselOf G P hE Om c f hS hW hψ) where
  eS := fun _ => 0
  eS_split := fun _ => ⟨∅, fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
  f := fun u _ => f.f1 u
  f_dual := fun u _ => f.free_flag_dual u
  mu1 := fun u _ => Measure.dirac 1
  mu_one_isHaarMeasure := fun u _ => dirac_haar (besselUnipotentSubgroup_zero_subsingleton (f.pos1 u).1 (f.f1 u))
  bper1 := fun u ho hr hA hι sF μ 𝓕 hp μN 𝓕N n1 n2 n3 s hs φ F hφ => by
    have e := besC_eq G P f.petF (f.pos1 u).1 hA hι μ 𝓕 hp (μN, 𝓕N) ⟨n1, n2, n3⟩ s hs φ F hφ
    refine e.trans (Eq.symm ((integral_dirac_one_of_subsingleton (besselUnipotentSubgroup_zero_subsingleton _ _) _).trans ?_))
    have hb : ∀ p, (besselOf G P hE Om c f hS hW hψ).besC (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) p = 1 := fun _ => rfl
    simp only [OneMemClass.coe_one, mul_one, hb, one_mul]
    rfl

def allCompatibilitiesOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) (h0 : TypZero D) (hA : TypAdd D)
    (hJ : FockCxEx D) (hD : PolAdd ψ) (hR : RealTied D) (A : ProvA) (hP : ProvisionCompatibility D A) : AllTied D (thetaOf D G P hE Om c f) A where
  T := thetaCompatibilityOf G P hE Om c f hS hW
  sm := allSome_fam.2 fun V _ => by
    ext φ
    exact ⟨fun ⟨F, hF⟩ => hF ▸ (mem_afC G.add).1 F.2, fun h => ⟨⟨φ, (mem_afC G.add).2 h⟩, rfl⟩⟩
  ty := allSome_fam.2 fun V hV Q hQ _ F => mem_typC h0 hA hV hQ
  W := weilCompatibilityOf G P hE Om c f hS hW hψ
  unr := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).unr
  kf :=
    { cpt := cptC
      cpt_gram := cptC_gram
      bas := basC
      bas_unit := fun V _ => basC_unit V
      bas_orth := fun V _ => basC_orth V
      cpt_bas := cptC_bas
      kfin := allSome_fam.2 fun V W a b d Φ => mem_kfinC hJ hD a b d Φ }
  phiUp := fun μ j hj x => swapC_apply ψ _ _ (rank_Y_ne (thetaOf D G P hE Om c f) j hj) (f.PhiY μ j) x
  B := besselOf G P hE Om c f hS hW hψ
  real := hR
  prov := hP

theorem allTied_thetaOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) (h0 : TypZero D) (hA : TypAdd D)
    (hJ : FockCxEx D) (hD : PolAdd ψ) (hR : RealTied D) (A : ProvA) (hP : ProvisionCompatibility D A) :
    Nonempty (AllTied D (thetaOf D G P hE Om c f) A) :=
  ⟨allCompatibilitiesOf G P hE Om c f hS hW hψ h0 hA hJ hD hR A hP⟩

end Ties

end Formalism.L2.Fam.ThC

end
