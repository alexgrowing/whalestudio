import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom basConj basConj_fix omTens pairAut realFac htStd IsFinK)
open scoped TensorProduct

namespace GlobalTheory.LocWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

variable {V : HSp D}

theorem conjDat_unit (c : ConjDat V) : IsUnit c.P.det := by
  have h := congrArg Matrix.det c.rel
  rw [Matrix.det_mul] at h
  have h2 : (V.gram.map (cE D)).det ≠ 0 := by
    have := (cE D).map_det V.gram
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).2 (gram_det_ne V)
  refine IsUnit.mk0 _ fun h0 => h2 ?_
  rw [← h, h0, mul_zero]

theorem ga_ext {g h : GA D V} (e : mt V g = mt V h) : g = h :=
  Subtype.ext (Units.ext e)

def invIsom (s : ConjIsom V) : ConjIsom V where
  P := (Matrix.GeneralLinearGroup.map (cE D) s.P)⁻¹
  iso := by
    set R : GL (Fin V.rank) D.host.E := Matrix.GeneralLinearGroup.map (cE D) s.P with hR
    have hab : s.P.val.map (cE D) * (R⁻¹).val = 1 := R.mul_inv
    have h := congrArg (fun M => M.map (cE D)) s.iso
    simp only [Matrix.map_mul] at h
    have e1 : (V.gram.map (cE D)).map (cE D) = V.gram := by funext i j; exact cE_cE _
    have e2 : (Formalism.UG.cT (cE D) s.P.val).map (cE D) = Formalism.UG.cT (cE D) (s.P.val.map (cE D)) := rfl
    rw [e1, e2] at h
    generalize (R⁻¹).val = B at *
    generalize s.P.val.map (cE D) = A at *
    calc Formalism.UG.cT (cE D) B * V.gram * B
        = Formalism.UG.cT (cE D) B * (Formalism.UG.cT (cE D) A * V.gram.map (cE D) * A) * B := by rw [h]
      _ = Formalism.UG.cT (cE D) (A * B) * V.gram.map (cE D) * (A * B) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

abbrev cG (D : D7) (n : ℕ) : GL (Fin n) (AE D) →* GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (cA D)

theorem cG_cG {n : ℕ} (g : GL (Fin n) (AE D)) : cG D n (cG D n g) = g := by
  ext i j; exact cA_cA _

theorem invIsom_PA (s : ConjIsom V) : (invIsom s).PA = (cG D _ s.PA)⁻¹ := by
  have : Matrix.GeneralLinearGroup.map (incA D) (Matrix.GeneralLinearGroup.map (cE D) s.P) = cG D _ s.PA := by
    ext i j; exact (cA_inc _).symm
  rw [← this, ← map_inv]; rfl

theorem matHom_aut (s : ConjIsom V) (g : GA D V) :
    matHom V (s.aut g) = s.PA * cG D _ (matHom V g) * s.PA⁻¹ := rfl

def autEquiv (s : ConjIsom V) : GA D V ≃* GA D V :=
  { s.aut with
    invFun := (invIsom s).aut
    left_inv := fun g => by
      apply Subtype.ext
      change matHom V ((invIsom s).aut (s.aut g)) = matHom V g
      rw [matHom_aut, matHom_aut, invIsom_PA, map_mul, map_mul, map_inv, cG_cG]
      group
    right_inv := fun g => by
      apply Subtype.ext
      change matHom V (s.aut ((invIsom s).aut g)) = matHom V g
      rw [matHom_aut, matHom_aut, invIsom_PA, map_mul, map_mul, map_inv, map_inv, map_inv, cG_cG, cG_cG]
      group }

def toDat (s : ConjIsom V) : ConjDat V where
  P := s.P.val
  rel := s.iso
  aut := autEquiv s
  aut_mt := fun g => by
    have : matHom V (s.aut g) * s.PA = s.PA * cG D _ (matHom V g) := by
      rw [matHom_aut, inv_mul_cancel_right]
    exact congrArg Units.val this

def ofDat (c : ConjDat V) : ConjIsom V where
  P := Matrix.nonsingInvUnit c.P (conjDat_unit c)
  iso := c.rel

theorem ofDat_aut (c : ConjDat V) (g : GA D V) : (ofDat c).aut g = c.aut g := by
  apply Subtype.ext
  change matHom V ((ofDat c).aut g) = matHom V (c.aut g)
  rw [matHom_aut, mul_inv_eq_iff_eq_mul]
  exact Units.ext (c.aut_mt g).symm

theorem isom_ext {s t : ConjIsom V} (h : s.P.val = t.P.val) : s = t := by
  cases s; cases t
  congr
  exact Units.ext h

def conjEquiv (V : HSp D) : ConjDat V ≃ ConjIsom V where
  toFun := ofDat
  invFun := toDat
  left_inv := fun c => by
    have h : (toDat (ofDat c)).aut = c.aut := MulEquiv.ext (ofDat_aut c)
    cases c
    unfold toDat at h ⊢
    congr
  right_inv := fun s => isom_ext rfl

theorem th_conj {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : IsInfEmb τ θ)
    (z : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z) := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hτ : ∀ x : D.host.E, τ (star x) = starRingEnd ℂ (τ x) := fun x =>
    IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hre : ∀ a : Ainf D.host.F, starRingEnd ℂ (θ (a ⊗ₜ[D.host.F] (1 : D.host.E))) =
      θ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro a
    refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
      (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
    have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
      exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
        (B := D.host.E)).commutes f |>.trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
    erw [e, h.1, ← hτ]
    rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a x =>
    have e : ∀ y : D.host.E, a ⊗ₜ[D.host.F] y =
        (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] (star x) := rfl
    rw [e2, e (star x), e x, map_mul, map_mul, map_mul, hre, h.1, h.1, hτ]

theorem infPart_cA (x : AE D) : infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem aut_mem_GinfC (s : ConjIsom V) {k : GA D V} (hk : k ∈ GinfC V) : s.aut k ∈ GinfC V := by
  have hk' : Formalism.UG.bc (finPart D) (matHom V k) = 1 := hk
  have h2 : Formalism.UG.bc (finPart D) (cG D _ (matHom V k)) = 1 := by
    apply Units.ext
    have h3 : (mt V k).map (finPart D) = 1 := congrArg Units.val hk'
    have h4 : ((mt V k).map (cA D)).map (finPart D) =
        ((mt V k).map (finPart D)).map (sigR (Af D.host.F) D.sp.cm.sig) := by
      funext i j; exact finPart_cA _
    change ((mt V k).map (cA D)).map (finPart D) = 1
    rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
  change Formalism.UG.bc (finPart D) (matHom V (s.aut k)) = 1
  rw [matHom_aut, map_mul, map_mul, h2, map_inv, mul_one, mul_inv_cancel]

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

variable (K : KfinTied Wl) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) (eG : ∀ V, L.G V ≃* GA D V)
  (eF : L.ChrF →* ((AF D.host.F)ˣ →* Circle))

abbrev IsVolMeasV (V : HSp D) (μ : Measure (GA D V)) : Prop :=
  IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ

def First : Prop :=
  ∃ h : Formalism.L2.Theta.LocWTied D X T Wl L, h.eG = eG ∧ h.eChrF = eF ∧ LocalWhittakerKFiniteCompatibility h K ∧ CjOfBas h K

def Second : Prop :=
  ∃ t : GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures.LocWTied K L, t.eG = eG ∧ t.eF = eF

structure Common : Prop where
  sR : L.sR = true
  meas : ∀ V, Measurable (eG V)
  gF : ∀ V g, g ∈ L.GF V ↔ eG V g ∈ GQ V
  gK : AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ g, g ∈ L.Gk V ↔ IsFinK θ V (K.cpt V) (eG V g)
  mu : ∃ c : HSp D → ℝ, (∀ V, 0 < c V) ∧ ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    Measure.map (eG V) (L.μG V) = ENNReal.ofReal (c V) • μ
  om : ∀ (V W : HSp D) (hV : V.SigOK) (hW : W.SigOK) χ χ', V.rank ≠ W.rank →
    ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ g h,
      L.om V W χ χ' (g, h) = omTens Wl (basConj K V hV) (basConj K W hW) χ χ' (eG V g, eG W h)
  thF : ∀ V W : HSp D, V.rank ≠ W.rank → ∀ Φ, L.thF V W Φ = Wl.evS V W Φ 0
  inj : Function.Injective eF
  mem : ∀ χ, Formalism.L2.Theta.IsHeckeCharF D (eF χ)
  res : ∀ χ a, eF (L.res χ) a = T.eChr χ (idF D a)
  eta : IsEta D (eF L.eta)
  cc : ∀ χ x, T.eChr (L.cc χ) x = T.eChr χ (conjId D x)

structure FirstOnly : Prop where
  thF : ∀ V W : HSp D, V.rank = W.rank → ∀ Φ, L.thF V W Φ = Wl.evS V W Φ 0
  om : ∃ cj : ∀ V : HSp D, ConjIsom V, (∀ V hV, cj V = basConj K V hV) ∧
    ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank →
      ¬ (V.SigOK ∧ W.SigOK ∧ ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank) → ∀ g h,
      L.om V W χ χ' (g, h) = omTens Wl (cj V) (cj W) χ χ' (eG V g, eG W h)

structure SecondOnly : Prop where
  measInv : ∀ V, Measurable (eG V).symm
  volEx : ∀ V : HSp D, V.SigOK → AllSome (IsVolMeasV V) fun μ => ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ
  prod : ∃ rc : ℕ → ℕ → NNReal, (∀ p q, 0 < rc p q) ∧ ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    Measure.map (eG V) (L.μG V) = realFac rc V • μ
  onto : ∀ χ, Formalism.L2.Theta.IsHeckeCharF D χ → ∃ x, eF x = χ
  ht : AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, ∃ (C : ℝ) (N : ℕ), ∀ g,
    L.ht V g ≤ C * htStd θ V (eG V g) ^ N ∧ htStd θ V (eG V g) ≤ C * L.ht V g ^ N

def flatHeight : Formalism.MainNotions.KudlaSiegelWeil.LocW D X :=
  { L with ht := fun _ _ => 1, ht_ge := fun _ _ => le_rfl, ht_mul := fun _ _ _ => by norm_num }

def scaleMeasure (c : HSp D → NNReal) : Formalism.MainNotions.KudlaSiegelWeil.LocW D X :=
  { L with μG := fun V => c V • L.μG V,
           Fd_fund := fun V => (L.Fd_fund V).mono Measure.smul_absolutelyContinuous }

end GlobalTheory.LocWCompare

end
