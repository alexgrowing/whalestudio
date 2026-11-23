import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Full

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.FinXP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Reps

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem lin_isom (s : TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem lin_lam (s : TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

theorem frame_eq (s : TT Y u u') :
    s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold GTerm.frame mapLF
  rw [dif_pos (lin_isom s)]
  rfl

theorem frame_apply (s : TT Y u u') (a : Fin (D.R.rS + 1)) :
    frame s.frame a = s.lin (frame (lf D (X.Fu u')) a) := by
  rw [frame_eq]
  exact congrFun (Formalism.L2.SG.Pf.frame_mapL' s.lin (lin_isom s) (lf D (X.Fu u'))) a

theorem dc_of_toTerm {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ TermDef.DCRel s.lam (lf D (X.Fu u)) s.frame s'.frame := by
  have hl : s.lam = s'.lam := congrArg TermDef.Term.lam h
  refine ⟨hl, ?_⟩
  have hc : HEq s.toTerm.cls s'.toTerm.cls := congr_arg_heq TermDef.Term.cls h
  have hrow : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have key : ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ₁ = Λ₂)
      (x : TermDef.Carrier (TermDef.PD D Λ₁ (lf D (X.Fu u)) u'))
      (y : TermDef.Carrier (TermDef.PD D Λ₂ (lf D (X.Fu u)) u')),
      HEq (TermDef.mk Λ₁ (lf D (X.Fu u)) _ x) (TermDef.mk Λ₂ (lf D (X.Fu u)) _ y) →
        IsRowLat D (X.Fu u) Λ₁ → TermDef.DCRel Λ₁ (lf D (X.Fu u)) x.1 y.1 := by
    intro Λ₁ Λ₂ hΛ x y hxy hr
    subst hΛ
    exact (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) Λ₁ hr x y).1 (eq_of_heq hxy)
  exact key s.lam s'.lam hl ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ hc hrow

theorem perpS_eq_orth (U : Submodule D.host.E (VS D).V) : perpS (VS D) U = orth (VS D) U := by
  ext x
  rw [Formalism.L2.SG.Pf.mem_orth']
  rfl

theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (he : ∀ a, c (F0.e a) = F0.e a) (hz : c F0.z = F0.z) :
    c ∈ stabF D F0 := by
  refine ⟨hc, fun j => ?_, hz⟩
  unfold FlagG.Xa
  rw [Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe, he]

theorem fix_X {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (he : ∀ a, c (F0.e a) = F0.e a) : ∀ x ∈ F0.X, c x = x := by
  intro x hx
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact he a
  | zero => simp
  | add y w _ _ hy hw => rw [map_add, hy, hw]
  | smul k y _ hy => rw [map_smul, hy]

end Reps

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem one_stabF {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 :=
  stabF_of_fix F0 1 (Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem (fun _ => rfl) rfl

theorem fib_decomp {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ s.lam' = s'.lam' ∧
    ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ m ∈ NLam s.lam s.frame, s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) ∧
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s.lam' = s.lam' ∧
      (∀ a, c ((X.Fu u').e a) = (X.Fu u').e a) ∧ c (X.Fu u').z = (X.Fu u').z ∧
      (∀ a, frame s'.frame a = n (m (frame s.frame a))) ∧ s'.frame.zt = n (m s.frame.zt) ∧
      s'.lin = n * m * s.lin * c := by
  obtain ⟨hl, n, hn, m, hm, hf, hzt⟩ := dc_of_toTerm h
  have hμN : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) := by
    have := (Formalism.L2.SG.Pf.mem_NLam_map s.lin (lin_isom s) s.lam' (lf D (X.Fu u')) m).1
    rw [lin_lam, ← frame_eq] at this
    exact this hm
  have hC : ∀ a, (s.lin⁻¹ * n⁻¹ * s'.lin) (frame (lf D (X.Fu u')) a) =
      (s.lin⁻¹ * m * s.lin) (frame (lf D (X.Fu u')) a) := by
    intro a
    have h1 : s'.lin (frame (lf D (X.Fu u')) a) = n (m (s.lin (frame (lf D (X.Fu u')) a))) := by
      rw [← frame_apply, ← frame_apply, hf a]
    show s.lin.symm (n.symm (s'.lin _)) = s.lin.symm (m (s.lin _))
    rw [h1, LinearEquiv.symm_apply_apply]
  set μ := s.lin⁻¹ * m * s.lin with hμ
  set c := μ⁻¹ * (s.lin⁻¹ * n⁻¹ * s'.lin) with hcdef
  have hcf : ∀ a, c (frame (lf D (X.Fu u')) a) = frame (lf D (X.Fu u')) a := by
    intro a
    show μ.symm ((s.lin⁻¹ * n⁻¹ * s'.lin) _) = _
    rw [hC a]
    exact μ.symm_apply_apply _
  have he : ∀ a, c ((X.Fu u').e a) = (X.Fu u').e a := by
    intro a
    have := hcf (Fin.castSucc a)
    rwa [Formalism.L2.SG.Pf.frame_castSucc_sat] at this
  have hz : c (X.Fu u').z = (X.Fu u').z := by
    have := hcf (Fin.last _)
    rwa [Formalism.L2.SG.Pf.frame_last_sat] at this
  have hiso : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    refine (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hμN.1.1) ?_
    exact (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
      ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem (lin_isom s)) ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1.1)) (lin_isom s')
  have hg : Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' := by
    rw [hcdef, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, lin_lam, ← hl,
      Formalism.L2.SG.Pf.gmap_inv hn.1.2, Formalism.L2.SG.Pf.gmap_inv (lin_lam s), Formalism.L2.SG.Pf.gmap_inv hμN.1.2]
  have hl' : s.lam' = s'.lam' := by
    have hrow : IsRowLat D (X.Fu u') s.lam' := (Y.rowsOK u').1 _ s.mem'
    exact ((Y.rowsOK u').2 s.lam' hrow).unique ⟨s.mem', 1, one_stabF _, Formalism.L2.SG.Pf.gmap_one _⟩
      ⟨s'.mem', c, stabF_of_fix _ c hiso he hz, hg⟩
  refine ⟨hl, hl', n, hn, m, hm, hμN, c, hiso, by rw [← hl'] at hg; exact hg, he, hz, hf, hzt, ?_⟩
  rw [hcdef, hμ]
  group

theorem gterm_eq {s s' : TT Y u u'} (h1 : s.lam = s'.lam) (h2 : s.lam' = s'.lam')
    (h3 : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') :
    s = s' := by
  obtain ⟨l, hl, l', hl', c⟩ := s
  obtain ⟨k, hk, k', hk', c'⟩ := s'
  simp only at h1 h2
  subst h1 h2
  have : c = c' := by
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    exact Quot.sound h3
  subst this
  rfl

def cPerp {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hX : ∀ x ∈ F0.X, c x = x) :
    perpS (VS D) F0.X →ₗ[D.host.E] perpS (VS D) F0.X :=
  ((c : (VS D).V →ₗ[D.host.E] (VS D).V).comp (perpS (VS D) F0.X).subtype).codRestrict (perpS (VS D) F0.X)
    (fun x => by
      intro y hy
      show (VS D).hT y (c x.1) = 0
      rw [← hX y hy, Formalism.L2.SG.Saturated.isom_apply hc]
      exact x.2 y hy)

def indW {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hX : ∀ x ∈ F0.X, c x = x) : WbQ D F0 →ₗ[D.host.E] WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    (cPerp F0 c hc hX) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
      show c x.1 ∈ F0.X
      rw [hX _ hx]; exact hx)

theorem indW_mk {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hX : ∀ x ∈ F0.X, c x = x) (x : perpS (VS D) F0.X) :
    indW F0 c hc hX (Submodule.Quotient.mk x) = Submodule.Quotient.mk (cPerp F0 c hc hX x) :=
  Submodule.mapQ_apply _ _ _ _

theorem indW_mem {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (he : ∀ a, c (F0.e a) = F0.e a) (hz : c F0.z = F0.z)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Formalism.HermitianLatticesTheory.gmap c Λ = Λ) :
    ⇑(indW F0 c hc (fix_X F0 c he)) ∈ autLz D F0 Λ := by
  refine ⟨c, stabF_of_fix F0 c hc he hz, hΛ, fun x hx => ?_⟩
  rw [indW_mk]
  rfl

theorem indW_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT} {hX : ∀ x ∈ F0.X, c x = x}
    {hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT} {hX' : ∀ x ∈ F0.X, c' x = x}
    (h : ⇑(indW F0 c hc hX) = ⇑(indW F0 c' hc' hX')) : ∀ x ∈ perpS (VS D) F0.X, c x - c' x ∈ F0.X := by
  intro x hx
  have h1 := congrFun h (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [indW_mk, indW_mk, Submodule.Quotient.eq] at h1
  exact h1

variable (Y) in
theorem fib_data (t : RT Y u u') (s₀ s : fib Y t) : ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V,
    c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.1.lam' = s₀.1.lam' ∧
      (∀ a, c ((X.Fu u').e a) = (X.Fu u').e a) ∧ c (X.Fu u').z = (X.Fu u').z ∧
      s.1.lam = s₀.1.lam ∧ s.1.lam' = s₀.1.lam' ∧
      ∃ n ∈ NLam s₀.1.lam (lf D (X.Fu u)), ∃ μ ∈ NLam s₀.1.lam' (lf D (X.Fu u')),
        s.1.lin = n * s₀.1.lin * μ * c := by
  obtain ⟨hl, hl', n, hn, m, -, hμ, c, hc, hg, he, hz, -, -, hs⟩ := fib_decomp (s₀.2.trans s.2.symm)
  refine ⟨c, hc, hg, he, hz, hl.symm, hl'.symm, n, hn, _, hμ, ?_⟩
  rw [hs]
  group

variable (Y) in

def cOf (t : RT Y u u') (s₀ s : fib Y t) : (VS D).V ≃ₗ[D.host.E] (VS D).V := Classical.choose (fib_data Y t s₀ s)

theorem cOf_spec (t : RT Y u u') (s₀ s : fib Y t) :
    cOf Y t s₀ s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap (cOf Y t s₀ s) s₀.1.lam' = s₀.1.lam' ∧
      (∀ a, cOf Y t s₀ s ((X.Fu u').e a) = (X.Fu u').e a) ∧ cOf Y t s₀ s (X.Fu u').z = (X.Fu u').z ∧
      s.1.lam = s₀.1.lam ∧ s.1.lam' = s₀.1.lam' ∧
      ∃ n ∈ NLam s₀.1.lam (lf D (X.Fu u)), ∃ μ ∈ NLam s₀.1.lam' (lf D (X.Fu u')),
        s.1.lin = n * s₀.1.lin * μ * cOf Y t s₀ s :=
  Classical.choose_spec (fib_data Y t s₀ s)

variable (Y) in

def phi (t : RT Y u u') (s₀ : fib Y t) (s : fib Y t) : autLz D (X.Fu u') s₀.1.lam' :=
  ⟨⇑(indW (X.Fu u') (cOf Y t s₀ s) (cOf_spec t s₀ s).1 (fix_X _ _ (cOf_spec t s₀ s).2.2.1)),
    indW_mem _ _ _ (cOf_spec t s₀ s).2.2.1 (cOf_spec t s₀ s).2.2.2.1 _ (cOf_spec t s₀ s).2.1⟩

theorem conj_fix_mem {Λ' : Submodule (𝓞 D.host.E) (VS D).V} {c ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Formalism.HermitianLatticesTheory.gmap c Λ' = Λ')
    (hX : ∀ x ∈ (X.Fu u').X, c x = x) (hν : ν ∈ NLam Λ' (lf D (X.Fu u'))) :
    c⁻¹ * ν * c ∈ NLam Λ' (lf D (X.Fu u')) := by
  have hXi : ∀ x ∈ (X.Fu u').X, c⁻¹ x = x := fun x hx => by
    show c.symm x = x
    rw [LinearEquiv.symm_apply_eq]; exact (hX x hx).symm
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
      ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hc) hν.1.1) hc, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, hg, hν.1.2, Formalism.L2.SG.Pf.gmap_inv hg]
  · have hxX : x ∈ (X.Fu u').X := Formalism.L2.SG.Pf.Xflag_le_X (lf D (X.Fu u')) _ hx
    have h1 := hν.2.1 j x hx
    have h1X : ν x - x ∈ (X.Fu u').X := Formalism.L2.SG.Pf.Xflag_le_X (lf D (X.Fu u')) _ h1
    have : (c⁻¹ * ν * c) x - x = c⁻¹ (ν x - x) := by
      rw [Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_mul_app, hX x hxX, map_sub, hXi x hxX]
    rw [this, hXi _ h1X]; exact h1
  · have hcx : c x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := by
      rw [Formalism.L2.SG.Pf.mem_orth'] at hx ⊢
      intro y hy
      rw [← hX y hy, Formalism.L2.SG.Saturated.isom_apply hc]; exact hx y hy
    have h1 := hν.2.2 (c x) hcx
    have : (c⁻¹ * ν * c) x - x = c⁻¹ (ν (c x) - c x) := by
      rw [Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_mul_app, map_sub]
      congr 1
      show x = c.symm (c x)
      rw [LinearEquiv.symm_apply_apply]
    rw [this, hXi _ h1]; exact h1

theorem phi_inj (t : RT Y u u') (s₀ : fib Y t) : Function.Injective (phi Y t s₀) := by
  intro s s' h
  obtain ⟨hc, hg, he, hz, hl, hl', n, hn, μ, hμ, hs⟩ := cOf_spec t s₀ s
  obtain ⟨hc', hg', he', hz', hk, hk', n', hn', μ', hμ', hs'⟩ := cOf_spec t s₀ s'
  have hW := indW_eq (X.Fu u') (congrArg Subtype.val h)
  set c := cOf Y t s₀ s
  set c' := cOf Y t s₀ s'
  have hX := fix_X (X.Fu u') c he
  have hX' := fix_X (X.Fu u') c' he'
  have hN : n' * n⁻¹ ∈ NLam s₀.1.lam (lf D (X.Fu u)) := Formalism.L2.SG.Pf.nlam_mul hn' (Formalism.L2.SG.Pf.nlam_inv hn)
  have hcc : c⁻¹ * c' ∈ NLam s₀.1.lam' (lf D (X.Fu u')) := by
    have hXi : ∀ x ∈ (X.Fu u').X, c⁻¹ x = x := fun x hx => by
      show c.symm x = x
      rw [LinearEquiv.symm_apply_eq]; exact (hX x hx).symm
    refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hc) hc', ?_⟩,
      fun j x hx => ?_, fun x hx => ?_⟩
    · rw [Formalism.L2.SG.Pf.gmap_mul, hg', Formalism.L2.SG.Pf.gmap_inv hg]
    · have hxX : x ∈ (X.Fu u').X := Formalism.L2.SG.Pf.Xflag_le_X (lf D (X.Fu u')) _ hx
      rw [Formalism.L2.SG.Pf.le_mul_app, hX' x hxX, hXi x hxX, sub_self]
      exact zero_mem _
    · have hxp : x ∈ perpS (VS D) (X.Fu u').X := by rw [perpS_eq_orth]; exact hx
      have h1 := hW x hxp
      have : (c⁻¹ * c') x - x = c⁻¹ (-(c x - c' x)) := by
        rw [Formalism.L2.SG.Pf.le_mul_app, map_neg, map_sub]
        show c.symm (c' x) - x = -(c.symm (c x) - c.symm (c' x))
        rw [LinearEquiv.symm_apply_apply]; abel
      rw [this, hXi _ (neg_mem h1)]; exact neg_mem h1
  have hN' : c⁻¹ * (μ⁻¹ * μ') * c * (c⁻¹ * c') ∈ NLam s₀.1.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlam_mul (conj_fix_mem hc hg hX (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hμ) hμ')) hcc
  apply Subtype.ext
  refine gterm_eq (hl.trans hk.symm) (hl'.trans hk'.symm) ⟨n' * n⁻¹, hl ▸ hN, c⁻¹ * (μ⁻¹ * μ') * c * (c⁻¹ * c'),
    hl' ▸ hN', ?_⟩
  rw [hs, hs']
  group

end Fib

theorem fibFin_holds : Formalism.L2.SG.TermTieOf.FibFinAll := by
  intro D X Y u u' t
  rcases isEmpty_or_nonempty (fib Y t) with h | h
  · infer_instance
  · obtain ⟨s₀⟩ := h
    have hrow : IsRowLat D (X.Fu u') s₀.1.lam' := (Y.rowsOK u').1 _ s₀.1.mem'
    have hA : (autLz D (X.Fu u') s₀.1.lam').Finite :=
      _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (X.Fu u') _ hrow
    haveI := hA.to_subtype
    exact Finite.of_injective (phi Y t s₀) (phi_inj t s₀)

section Move

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem orth_anti {U W : Submodule E S.V} (h : U ≤ W) : orth S W ≤ orth S U := by
  intro x hx
  rw [mem_orth'] at hx ⊢
  exact fun y hy => hx y (h hy)

theorem XLamF_le_UU (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : XLam Λ F ≤ UU Λ F F' := by
  unfold UU
  exact le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem XLamG_le_UU (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : XLam Λ F' ≤ UU Λ F F' := by
  unfold UU
  exact le_sup_right.trans le_sup_left

theorem Hp_le_orthF {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} (F' : LFlag S r T')
    (hs : Xsp F ≤ spanE S (XLam Λ F)) : Hp Λ F F' ≤ orth S (Xsp F) :=
  orth_anti (hs.trans (Submodule.span_mono (fun x hx => XLamF_le_UU Λ F F' hx)))

theorem Hp_le_orthG {Λ : Submodule (𝓞 E) S.V} (F : LFlag S r T) {F' : LFlag S r T'}
    (hs : Xsp F' ≤ spanE S (XLam Λ F')) : Hp Λ F F' ≤ orth S (Xsp F') :=
  orth_anti (hs.trans (Submodule.span_mono (fun x hx => XLamG_le_UU Λ F F' hx)))

theorem UUE_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ G) (hf : ∀ a, frame K a = n (m (frame G a))) (hz : K.zt = n (m G.zt))
    (hLF : IsLift Λ F) (hLG : IsLift Λ G) :
    UUE Λ F K = (UUE Λ F G).map (n : S.V →ₗ[E] S.V) := by
  unfold UUE
  rw [UU_DC hn hm hf hz hLF hLG, spanE_gmap n]

theorem Hp_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ G) (hf : ∀ a, frame K a = n (m (frame G a))) (hz : K.zt = n (m G.zt))
    (hLF : IsLift Λ F) (hLG : IsLift Λ G) :
    Hp Λ F K = (Hp Λ F G).map (n : S.V →ₗ[E] S.V) := by
  unfold Hp
  rw [UUE_move hn hm hf hz hLF hLG, orth_map_sat n hn.1.1]

theorem mem_map_iff (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (x : S.V) :
    x ∈ U.map (n : S.V →ₗ[E] S.V) ↔ n.symm x ∈ U := Submodule.mem_map_equiv U

theorem key_mod {Λ : Submodule (𝓞 E) S.V} {G₁ G₂ : LFlag S r T'} {m₁ m₂ β τ : S.V ≃ₗ[E] S.V}
    (hm₁ : m₁ ∈ NLam Λ G₁) (hm₂ : m₂ ∈ NLam Λ G₂)
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβX : (Xsp G₁).map (β : S.V →ₗ[E] S.V) = Xsp G₂)
    (hτX : ∀ x ∈ Xsp G₁, τ x ∈ Xsp G₁) (hτ : ∀ x ∈ orth S (Xsp G₁), τ x - x ∈ Xsp G₁)
    {x : S.V} (hx : x ∈ orth S (Xsp G₁)) : m₂ (β (τ (m₁.symm x))) - β x ∈ Xsp G₂ := by
  have hmi := nlam_inv hm₁
  have h1 : m₁.symm x - x ∈ Xsp G₁ := hmi.2.2 x hx
  have h2 : τ (m₁.symm x) - x ∈ Xsp G₁ := by
    have : τ (m₁.symm x) - x = (τ x - x) + τ (m₁.symm x - x) := by rw [map_sub]; abel
    rw [this]; exact add_mem (hτ x hx) (hτX _ h1)
  have hβmem : ∀ y ∈ Xsp G₁, β y ∈ Xsp G₂ := fun y hy => hβX ▸ Submodule.mem_map_of_mem hy
  have h3 : β (τ (m₁.symm x)) - β x ∈ Xsp G₂ := by rw [← map_sub]; exact hβmem _ h2
  have h4 : β x ∈ orth S (Xsp G₂) := by
    rw [mem_orth'] at hx ⊢
    intro y hy
    rw [← hβX] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    show S.hT (β y0) (β x) = 0
    rw [Formalism.L2.SG.Saturated.isom_apply hβ]; exact hx y0 hy0
  have h5 : β (τ (m₁.symm x)) ∈ orth S (Xsp G₂) := by
    have : β (τ (m₁.symm x)) = β x + (β (τ (m₁.symm x)) - β x) := by abel
    rw [this]; exact add_mem h4 (X_le_orth_sat G₂ h3)
  have h6 := hm₂.2.2 _ h5
  have : m₂ (β (τ (m₁.symm x))) - β x =
      (m₂ (β (τ (m₁.symm x))) - β (τ (m₁.symm x))) + (β (τ (m₁.symm x)) - β x) := by abel
  rw [this]; exact add_mem h6 h3

theorem mem_ThPairs {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}
    (p : S.V × S.V) : p ∈ ThPairs Λ F F' F'' β ↔ p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'' ∧ p.1 - p.2 ∈ Xsp F ∧
      β p.1 - p.2 ∈ Xsp F'' := by
  unfold ThPairs
  simp only [Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  tauto

theorem mem_Th {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}
    (y : S.V) : y ∈ Th Λ F F' F'' β ↔ ∃ y₂, (y, y₂) ∈ ThPairs Λ F F' F'' β := by
  unfold Th
  simp only [Submodule.mem_map, LinearMap.fst_apply, Prod.exists]
  constructor
  · rintro ⟨a, b, h, rfl⟩; exact ⟨b, h⟩
  · rintro ⟨b, h⟩; exact ⟨y, b, h, rfl⟩

theorem Th_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G₁ G₂ K₁ K₂ : LFlag S r T'}
    {n₁ n₂ m₁ m₂ β τ : S.V ≃ₗ[E] S.V}
    (hn₁ : n₁ ∈ NLam Λ F) (hn₂ : n₂ ∈ NLam Λ F) (hm₁ : m₁ ∈ NLam Λ G₁) (hm₂ : m₂ ∈ NLam Λ G₂)
    (hf₁ : ∀ a, frame K₁ a = n₁ (m₁ (frame G₁ a))) (hz₁ : K₁.zt = n₁ (m₁ G₁.zt))
    (hf₂ : ∀ a, frame K₂ a = n₂ (m₂ (frame G₂ a))) (hz₂ : K₂.zt = n₂ (m₂ G₂.zt))
    (hLF : IsLift Λ F) (hL₁ : IsLift Λ G₁) (hL₂ : IsLift Λ G₂)
    (hsF : Xsp F ≤ spanE S (XLam Λ F)) (hs₁ : Xsp G₁ ≤ spanE S (XLam Λ G₁))
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβX : (Xsp G₁).map (β : S.V →ₗ[E] S.V) = Xsp G₂)
    (hτX : ∀ x ∈ Xsp G₁, τ x ∈ Xsp G₁) (hτ : ∀ x ∈ orth S (Xsp G₁), τ x - x ∈ Xsp G₁) :
    Th Λ F K₁ K₂ (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) = (Th Λ F G₁ G₂ β).map (n₁ : S.V →ₗ[E] S.V) := by
  have hH₁ := Hp_move hn₁ hm₁ hf₁ hz₁ hLF hL₁
  have hH₂ := Hp_move hn₂ hm₂ hf₂ hz₂ hLF hL₂
  have hX₂ : Xsp K₂ = (Xsp G₂).map (n₂ : S.V →ₗ[E] S.V) := Xsp_DC hm₂ hf₂
  have happ : ∀ x, (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) (n₁ x) = n₂ (m₂ (β (τ (m₁.symm x)))) := by
    intro x
    show n₂ (m₂ (β (τ (m₁.symm (n₁.symm (n₁ x)))))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hXX : ∀ {x₁ x₂ : S.V}, x₁ ∈ orth S (Xsp F) → x₂ ∈ orth S (Xsp F) →
      (n₁ x₁ - n₂ x₂ ∈ Xsp F ↔ x₁ - x₂ ∈ Xsp F) := by
    intro x₁ x₂ h1 h2
    have a := hn₁.2.2 x₁ h1
    have b := hn₂.2.2 x₂ h2
    constructor
    · intro c
      have : x₁ - x₂ = (n₁ x₁ - n₂ x₂) - (n₁ x₁ - x₁) + (n₂ x₂ - x₂) := by abel
      rw [this]; exact add_mem (sub_mem c a) b
    · intro c
      have : n₁ x₁ - n₂ x₂ = (x₁ - x₂) + (n₁ x₁ - x₁) - (n₂ x₂ - x₂) := by abel
      rw [this]; exact sub_mem (add_mem c a) b
  ext y
  rw [mem_Th, Submodule.mem_map]
  constructor
  · rintro ⟨y₂, hp⟩
    rw [mem_ThPairs] at hp
    obtain ⟨hy, hy₂, h12, hb⟩ := hp
    rw [hH₁, mem_map_iff] at hy
    rw [hH₂, mem_map_iff] at hy₂
    refine ⟨n₁.symm y, ?_, n₁.apply_symm_apply y⟩
    rw [mem_Th]
    refine ⟨n₂.symm y₂, ?_⟩
    rw [mem_ThPairs]
    have e1 : n₁ (n₁.symm y) = y := n₁.apply_symm_apply y
    have e2 : n₂ (n₂.symm y₂) = y₂ := n₂.apply_symm_apply y₂
    refine ⟨hy, hy₂, (hXX (Hp_le_orthF _ hsF hy) (Hp_le_orthF _ hsF hy₂)).1 (by rw [e1, e2]; exact h12), ?_⟩
    set x₁ := n₁.symm y with hx₁def
    set x₂ := n₂.symm y₂ with hx₂def
    have hx₁ : x₁ ∈ Hp Λ F G₁ := hy
    rw [← e1, ← e2, happ, hX₂, mem_map_iff, map_sub, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hb
    have hk := key_mod hm₁ hm₂ hβ hβX hτX hτ (Hp_le_orthG F hs₁ hx₁)
    have : β x₁ - x₂ = (m₂ (β (τ (m₁.symm x₁))) - x₂) - (m₂ (β (τ (m₁.symm x₁))) - β x₁) := by abel
    rw [this]; exact sub_mem hb hk
  · rintro ⟨x₁, hx, rfl⟩
    rw [mem_Th] at hx
    obtain ⟨x₂, hp⟩ := hx
    rw [mem_ThPairs] at hp
    obtain ⟨hx₁, hx₂, h12, hb⟩ := hp
    refine ⟨n₂ x₂, ?_⟩
    rw [mem_ThPairs]
    refine ⟨hH₁ ▸ Submodule.mem_map_of_mem hx₁, hH₂ ▸ Submodule.mem_map_of_mem hx₂,
      (hXX (Hp_le_orthF _ hsF hx₁) (Hp_le_orthF _ hsF hx₂)).2 h12, ?_⟩
    show (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) (n₁ x₁) - n₂ x₂ ∈ Xsp K₂
    rw [happ, hX₂, mem_map_iff, map_sub, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have hk := key_mod hm₁ hm₂ hβ hβX hτX hτ (Hp_le_orthG F hs₁ hx₁)
    have : m₂ (β (τ (m₁.symm x₁))) - x₂ = (m₂ (β (τ (m₁.symm x₁))) - β x₁) + (β x₁ - x₂) := by abel
    rw [this]; exact add_mem hk hb

theorem xplus_nlam {Λ : Submodule (𝓞 E) S.V} {G : LFlag S r T'} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G)
    {w : S.V} (hw : w ∈ Xplus G) : n w ∈ Xplus G := by
  unfold Xplus FlagG.Xplus at hw ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hz := hn.2.2 _ (isotropicSpan_orthogonal_anisotropicVector G)
  have hxX : n x ∈ Xsp G := nlam_presX hn x hx
  refine Submodule.mem_sup.2 ⟨n x + c • (n G.fl.z - G.fl.z), add_mem hxX (Submodule.smul_mem _ c hz), c • G.fl.z,
    Submodule.mem_span_singleton.2 ⟨c, rfl⟩, ?_⟩
  rw [map_add, map_smul]
  module

theorem map_X_of_e {G K : LFlag S r T'} {φ : S.V ≃ₗ[E] S.V} (he : ∀ a, φ (G.fl.e a) = K.fl.e a) {x : S.V}
    (hx : x ∈ G.fl.X) : φ x ∈ K.fl.X := by
  unfold FlagG.X at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; rw [he]; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => simp
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | smul k y _ hy => rw [map_smul]; exact Submodule.smul_mem _ k hy

theorem xplus_frame {G K : LFlag S r T'} {φ : S.V ≃ₗ[E] S.V} (hf : ∀ a, frame K a = φ (frame G a))
    {w : S.V} (hw : w ∈ Xplus G) : φ w ∈ Xplus K := by
  unfold Xplus FlagG.Xplus at hw ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have he : ∀ a, φ (G.fl.e a) = K.fl.e a := fun a => by
    have := hf (Fin.castSucc a)
    rw [frame_castSucc_sat, frame_castSucc_sat] at this; exact this.symm
  have hz : φ G.fl.z = K.fl.z := by
    have := hf (Fin.last _)
    rw [frame_last_sat, frame_last_sat] at this; exact this.symm
  have hxK : φ x ∈ K.fl.X := map_X_of_e he hx
  rw [map_add, map_smul, hz]
  exact add_mem (Submodule.mem_sup_left hxK) (Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨c, rfl⟩))

theorem orth_pull {U : Submodule E S.V} {φ : S.V ≃ₗ[E] S.V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (W : Submodule E S.V)
    (hUW : ∀ w ∈ U, φ w ∈ W) {y : S.V} (hy : y ∈ orth S W) : φ.symm y ∈ orth S U := by
  rw [mem_orth'] at hy ⊢
  intro w hw
  rw [← Formalism.L2.SG.Saturated.isom_apply hφ, LinearEquiv.apply_symm_apply]
  exact hy _ (hUW w hw)

theorem sg_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G K : LFlag S r T'} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (hX : Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V)) (hz : K.zt - n G.zt ∈ Xsp K)
    (hLF : IsLift Λ F) (y y' : S.V) (al al' : E) :
    SgRel F K (n y) (n y') al al' ↔ SgRel F G y y' al al' := by
  have hzF : n F.zt - F.zt ∈ Xsp F := by rw [hLF.2]; exact hn.2.2 _ (isotropicSpan_orthogonal_anisotropicVector F)
  have hni := nlam_inv hn
  have hzFi : n.symm F.zt - F.zt ∈ Xsp F := by rw [hLF.2]; exact hni.2.2 _ (isotropicSpan_orthogonal_anisotropicVector F)
  constructor
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨al • (n.symm F.zt - F.zt) + n.symm x, add_mem (Submodule.smul_mem _ _ hzFi) (nlam_presX hni x hx),
      al' • n.symm (K.zt - n G.zt) + n.symm x', ?_, ?_⟩
    · have h1 : n.symm (K.zt - n G.zt) ∈ Xsp G := (mem_map_iff n _ _).1 (hX ▸ hz)
      have h2 : n.symm x' ∈ Xsp G := (mem_map_iff n _ _).1 (hX ▸ hx')
      exact add_mem (Submodule.smul_mem _ _ h1) h2
    · have e : y - y' = n.symm (n y - n y') := by rw [map_sub, n.symm_apply_apply, n.symm_apply_apply]
      rw [e, h]
      simp only [map_add, map_smul, map_sub, n.symm_apply_apply]
      module
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨al • (n F.zt - F.zt) + n x, add_mem (Submodule.smul_mem _ _ hzF) (nlam_presX hn x hx),
      n x' - al' • (K.zt - n G.zt), sub_mem (hX ▸ Submodule.mem_map_of_mem hx') (Submodule.smul_mem _ _ hz), ?_⟩
    rw [← map_sub, h]
    simp only [map_add, map_smul]
    module

theorem scal_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G₁ G₂ K₁ K₂ : LFlag S r T'}
    {n₁ n₂ m₁ m₂ β τ : S.V ≃ₗ[E] S.V}
    (hn₁ : n₁ ∈ NLam Λ F) (hn₂ : n₂ ∈ NLam Λ F) (hm₁ : m₁ ∈ NLam Λ G₁) (hm₂ : m₂ ∈ NLam Λ G₂)
    (hf₁ : ∀ a, frame K₁ a = n₁ (m₁ (frame G₁ a))) (hz₁ : K₁.zt = n₁ (m₁ G₁.zt))
    (hf₂ : ∀ a, frame K₂ a = n₂ (m₂ (frame G₂ a))) (hz₂ : K₂.zt = n₂ (m₂ G₂.zt))
    (hLF : IsLift Λ F) (hL₁ : IsLift Λ G₁) (hL₂ : IsLift Λ G₂)
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβX : (Xsp G₁).map (β : S.V →ₗ[E] S.V) = Xsp G₂)
    (hτX : ∀ x ∈ Xsp G₁, τ x ∈ Xsp G₁) (hτ : ∀ x ∈ orth S (Xsp G₁), τ x - x ∈ Xsp G₁)
    (hS : IsScalar Λ F G₁ G₂ β) : IsScalar Λ F K₁ K₂ (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) := by
  have hU₁ := UUE_move hn₁ hm₁ hf₁ hz₁ hLF hL₁
  have hU₂ := UUE_move hn₂ hm₂ hf₂ hz₂ hLF hL₂
  have hX₁ : Xsp K₁ = (Xsp G₁).map (n₁ : S.V →ₗ[E] S.V) := Xsp_DC hm₁ hf₁
  have hX₂ : Xsp K₂ = (Xsp G₂).map (n₂ : S.V →ₗ[E] S.V) := Xsp_DC hm₂ hf₂
  have hzK : ∀ {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}, m ∈ NLam Λ G → IsLift Λ G →
      Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V) → K.zt = n (m G.zt) → K.zt - n G.zt ∈ Xsp K := by
    intro G K n m hm hL hX hz
    rw [hz, ← map_sub, hX]
    refine Submodule.mem_map_of_mem ?_
    rw [hL.2]; exact hm.2.2 _ (isotropicSpan_orthogonal_anisotropicVector G)
  have hpF : ∀ {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F → ∀ {y : S.V}, y ∈ orth S (Xplus F) → n.symm y ∈ orth S (Xplus F) := by
    intro n hn y hy
    exact orth_pull hn.1.1 _ (fun w hw => xplus_nlam hn hw) hy
  have hpG : ∀ {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F → m ∈ NLam Λ G →
      (∀ a, frame K a = n (m (frame G a))) → ∀ {y : S.V}, y ∈ orth S (Xplus K) → n.symm y ∈ orth S (Xplus G) := by
    intro G K n m hn hm hf y hy
    refine orth_pull hn.1.1 _ (fun w hw => ?_) hy
    have h1 : m.symm w ∈ Xplus G := xplus_nlam (nlam_inv hm) hw
    have h2 := xplus_frame (φ := n * m) (fun a => hf a) h1
    have : (n * m) (m.symm w) = n w := by show n (m (m.symm w)) = n w; rw [LinearEquiv.apply_symm_apply]
    rwa [this] at h2
  have hoX : orth S (Xplus F) ≤ orth S (Xsp F) := orth_anti le_sup_left
  have hoX' : ∀ (G : LFlag S r T'), orth S (Xplus G) ≤ orth S (Xsp G) := fun G => orth_anti le_sup_left
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h2'' al al'
  have hY1 : n₁.symm y1 ∈ Ylift Λ F G₁ :=
    ⟨(mem_map_iff n₁ _ _).1 (hU₁ ▸ hy1.1), hpF hn₁ hy1.2⟩
  have hY2 : n₂.symm y2 ∈ Ylift Λ F G₂ :=
    ⟨(mem_map_iff n₂ _ _).1 (hU₂ ▸ hy2.1), hpF hn₂ hy2.2⟩
  have hY1' : n₁.symm y1' ∈ Ylift' Λ F G₁ :=
    ⟨(mem_map_iff n₁ _ _).1 (hU₁ ▸ hy1'.1), hpG hn₁ hm₁ hf₁ hy1'.2⟩
  have hY2'' : n₂.symm y2'' ∈ Ylift' Λ F G₂ :=
    ⟨(mem_map_iff n₂ _ _).1 (hU₂ ▸ hy2''.1), hpG hn₂ hm₂ hf₂ hy2''.2⟩
  have hc12 : n₁.symm y1 - n₂.symm y2 ∈ Xsp F := by
    have a := (nlam_inv hn₁).2.2 y1 (hoX hy1.2)
    have b := (nlam_inv hn₂).2.2 y2 (hoX hy2.2)
    have : n₁.symm y1 - n₂.symm y2 = (n₁⁻¹ y1 - y1) - (n₂⁻¹ y2 - y2) + (y1 - y2) := by
      show _ = (n₁.symm y1 - y1) - (n₂.symm y2 - y2) + (y1 - y2); abel
    rw [this]; exact add_mem (sub_mem a b) h12
  have hc2 : n₂.symm y2'' - β (n₁.symm y1') ∈ Xsp G₂ := by
    have h0 : y2'' - (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) y1' ∈ Xsp K₂ := h2''
    have happ : (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) y1' = n₂ (m₂ (β (τ (m₁.symm (n₁.symm y1'))))) := rfl
    rw [happ, hX₂, mem_map_iff, map_sub, LinearEquiv.symm_apply_apply] at h0
    have hk := key_mod hm₁ hm₂ hβ hβX hτX hτ (hoX' _ hY1'.2)
    have : n₂.symm y2'' - β (n₁.symm y1') =
        (n₂.symm y2'' - m₂ (β (τ (m₁.symm (n₁.symm y1'))))) + (m₂ (β (τ (m₁.symm (n₁.symm y1')))) - β (n₁.symm y1')) := by
      abel
    rw [this]; exact add_mem h0 hk
  have key := hS _ hY1 _ hY2 _ hY1' _ hY2'' hc12 hc2 al al'
  have s1 := sg_move hn₁ hX₁ (hzK hm₁ hL₁ hX₁ hz₁) hLF (n₁.symm y1) (n₁.symm y1') al al'
  have s2 := sg_move hn₂ hX₂ (hzK hm₂ hL₂ hX₂ hz₂) hLF (n₂.symm y2) (n₂.symm y2'') al al'
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at s1 s2
  exact s1.trans (key.trans s2.symm)

end Move

def IotaKer : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s₁ s₂ t₁ t₂ : TT Y u u')
    (n₁ n₂ m₁ m₂ c₁ c₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    s₂.lam = s₁.lam → t₁.lam = s₁.lam → t₂.lam = s₁.lam →
    s₂.lam' = s₁.lam' → t₁.lam' = s₁.lam' → t₂.lam' = s₁.lam' →
    n₁ ∈ NLam s₁.lam (lf D (X.Fu u)) → n₂ ∈ NLam s₁.lam (lf D (X.Fu u)) →
    m₁ ∈ NLam s₁.lam s₁.frame → m₂ ∈ NLam s₁.lam s₂.frame →
    c₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → c₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    Formalism.HermitianLatticesTheory.gmap c₁ s₁.lam' = s₁.lam' → Formalism.HermitianLatticesTheory.gmap c₂ s₁.lam' = s₁.lam' →
    (∀ a, c₁ ((X.Fu u').e a) = (X.Fu u').e a) → (∀ a, c₂ ((X.Fu u').e a) = (X.Fu u').e a) →
    c₁ (X.Fu u').z = (X.Fu u').z → c₂ (X.Fu u').z = (X.Fu u').z →
    t₁.lin = n₁ * m₁ * s₁.lin * c₁ → t₂.lin = n₂ * m₂ * s₂.lin * c₂ →
    iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ →
    iotaOf Y.TR (Y.cs u) (Y.cs u') t₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') t₂ →
    ∀ x ∈ orth (VS D) (X.Fu u').X, (c₂ * c₁⁻¹) x - x ∈ (X.Fu u').X

section Pair

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem X_le_spanE_XLam {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (h : IsRowLat D F0 Λ) : Xsp (lf D F0) ≤ spanE (VS D) (XLam Λ (lf D F0)) := by
  rw [h.2.2]
  show Submodule.span D.host.E (Set.range F0.e) ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span (Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F0 a)

theorem Xsp_frame (s : TT Y u u') : Xsp s.frame = (Xsp (lf D (X.Fu u'))).map (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [frame_eq]
  exact Xsp_mapL s.lin (lin_isom s) (lf D (X.Fu u'))

theorem hs_frame (s : TT Y u u') : Xsp s.frame ≤ spanE (VS D) (XLam s.lam s.frame) := by
  have hrow : IsRowLat D (X.Fu u') s.lam' := (Y.rowsOK u').1 _ s.mem'
  have h0 := X_le_spanE_XLam (X.Fu u') s.lam' hrow
  have e1 : XLam s.lam s.frame = Formalism.HermitianLatticesTheory.gmap s.lin (XLam s.lam' (lf D (X.Fu u'))) := by
    have := XLam_mapL s.lin (lin_isom s) s.lam' (lf D (X.Fu u'))
    rw [lin_lam, ← frame_eq] at this
    exact this
  rw [e1, spanE_gmap, Xsp_frame]
  exact Submodule.map_mono h0

theorem lift_F (s : TT Y u u') : IsLift s.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 _ s.mem).2.1.2.2.1

theorem lift_frame (s : TT Y u u') : IsLift s.lam s.frame := s.rep.2.2.2.2.1

def TrivW (U : Submodule D.host.E (VS D).V) (φ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  (∀ x ∈ U, φ x ∈ U) ∧ ∀ x ∈ orth (VS D) U, φ x - x ∈ U

theorem conj_triv {U : Submodule D.host.E (VS D).V} {l φ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hl : l ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hφ : TrivW U φ) :
    (∀ x ∈ U.map (l : (VS D).V →ₗ[D.host.E] (VS D).V), (l * φ * l⁻¹) x ∈ U.map (l : (VS D).V →ₗ[D.host.E] (VS D).V)) ∧
    ∀ x ∈ orth (VS D) (U.map (l : (VS D).V →ₗ[D.host.E] (VS D).V)),
      (l * φ * l⁻¹) x - x ∈ U.map (l : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have happ : ∀ x, (l * φ * l⁻¹) x = l (φ (l.symm x)) := fun x => rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_map_iff] at hx ⊢
    rw [happ, l.symm_apply_apply]
    exact hφ.1 _ hx
  · rw [orth_map_sat l hl, mem_map_iff] at hx
    rw [mem_map_iff, happ, map_sub, l.symm_apply_apply]
    exact hφ.2 _ hx

set_option maxHeartbeats 400000 in

theorem pair_step (hK : IotaKer) {s₁ s₂ t₁ t₂ : TT Y u u'} (h1 : s₁.toTerm = t₁.toTerm) (h2 : s₂.toTerm = t₂.toTerm)
    (hr : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂)
    (hr' : rowOf Y.TR (Y.cs u) (Y.cs u') t₁ = rowOf Y.TR (Y.cs u) (Y.cs u') t₂) :
    s0T s₁ s₂ = s0T t₁ t₂ ∧ (liftScalar s₁ s₂ → liftScalar t₁ t₂) := by
  obtain ⟨hl1, hl1', n₁, hn₁, m₁, hm₁, hμ₁, c₁, hc₁, hg₁, he₁, hz₁, hf₁, hzt₁, hlin₁⟩ := fib_decomp h1
  obtain ⟨hl2, hl2', n₂, hn₂, m₂, hm₂, hμ₂, c₂, hc₂, hg₂, he₂, hz₂, hf₂, hzt₂, hlin₂⟩ := fib_decomp h2
  have hl : s₁.lam = s₂.lam := congrArg (fun q => q.1.1) hr
  have hl' : s₁.lam' = s₂.lam' := congrArg (fun q => q.2.1.1) hr
  have hι : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ := congrArg (fun q => q.2.2) hr
  have hm : t₁.lam = t₂.lam := congrArg (fun q => q.1.1) hr'
  have hm' : t₁.lam' = t₂.lam' := congrArg (fun q => q.2.1.1) hr'
  have hι' : iotaOf Y.TR (Y.cs u) (Y.cs u') t₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') t₂ := congrArg (fun q => q.2.2) hr'
  have hn₂' : n₂ ∈ NLam s₁.lam (lf D (X.Fu u)) := by rw [hl]; exact hn₂
  have hm₂' : m₂ ∈ NLam s₁.lam s₂.frame := by rw [hl]; exact hm₂
  have hμ₂' : s₂.lin⁻¹ * m₂ * s₂.lin ∈ NLam s₁.lam' (lf D (X.Fu u')) := by rw [hl']; exact hμ₂
  have hg₂' : Formalism.HermitianLatticesTheory.gmap c₂ s₁.lam' = s₁.lam' := by rw [hl']; exact hg₂
  have hm₂s : m₂ ∈ NLam s₁.lam s₂.frame := hm₂'
  have hker := hK D X Y u u' s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂
    hl.symm hl1.symm (hl2.symm.trans hl.symm) hl'.symm hl1'.symm (hl2'.symm.trans hl'.symm) hn₁ hn₂' hm₁ hm₂s
    hc₁ hc₂ hg₁ hg₂' he₁ he₂ hz₁ hz₂ hlin₁ hlin₂ hι hι'

  have hcc : TrivW (Xsp (lf D (X.Fu u'))) (c₂ * c₁⁻¹) := by
    refine ⟨fun x hx => ?_, hker⟩
    have h1 : c₁⁻¹ x = x := by
      show c₁.symm x = x
      rw [LinearEquiv.symm_apply_eq]; exact (fix_X (X.Fu u') c₁ he₁ x hx).symm
    show c₂ (c₁⁻¹ x) ∈ _
    rw [h1, fix_X (X.Fu u') c₂ he₂ x hx]; exact hx
  obtain ⟨hτX, hτ⟩ := conj_triv (lin_isom s₁) hcc
  rw [← Xsp_frame] at hτX hτ

  have hβt : t₂.lin * t₁.lin⁻¹ =
      n₂ * m₂ * (s₂.lin * s₁.lin⁻¹) * (s₁.lin * (c₂ * c₁⁻¹) * s₁.lin⁻¹) * m₁⁻¹ * n₁⁻¹ := by
    rw [hlin₁, hlin₂]; group
  have hβ : s₂.lin * s₁.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem (lin_isom s₂) ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem (lin_isom s₁))
  have hβX : (Xsp s₁.frame).map ((s₂.lin * s₁.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Xsp s₂.frame := by
    rw [Xsp_frame, Xsp_frame]
    ext y
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨x0, hx0, rfl⟩, rfl⟩
      refine ⟨x0, hx0, ?_⟩
      show s₂.lin x0 = s₂.lin (s₁.lin.symm (s₁.lin x0))
      rw [LinearEquiv.symm_apply_apply]
    · rintro ⟨x0, hx0, rfl⟩
      refine ⟨s₁.lin x0, ⟨x0, hx0, rfl⟩, ?_⟩
      show s₂.lin (s₁.lin.symm (s₁.lin x0)) = s₂.lin x0
      rw [LinearEquiv.symm_apply_apply]
  have hL₂ : IsLift s₁.lam s₂.frame := by rw [hl]; exact lift_frame s₂
  have hsF := X_le_spanE_XLam (X.Fu u) s₁.lam ((Y.rowsOK u).1 _ s₁.mem)
  constructor
  · unfold s0T
    rw [if_pos ⟨hl, hl'⟩, if_pos ⟨hm, hm'⟩, ← hl1, hβt]
    have hT := Th_move hn₁ hn₂' hm₁ hm₂' hf₁ hzt₁ hf₂ hzt₂ (lift_F s₁) (lift_frame s₁) hL₂ hsF (hs_frame s₁) hβ hβX
      hτX hτ
    unfold Lat.s0
    exact congrArg (fun q : ℕ => D.R.k - q) ((LinearEquiv.finrank_map_eq n₁ _).symm.trans
      (congrArg (fun M : Submodule D.host.E (VS D).V => Module.finrank D.host.E M) hT).symm)
  · unfold liftScalar
    intro hS
    rw [← hl1, hβt]
    exact scal_move hn₁ hn₂' hm₁ hm₂' hf₁ hzt₁ hf₂ hzt₂ (lift_F s₁) (lift_frame s₁) hL₂ hβ hβX hτX hτ hS

end Pair

theorem pairIndep_of (hK : IotaKer) : Formalism.L2.SG.TermTieOf.PairIndepAll := by
  intro D X Y u u' s₁ s₂ s₁' s₂' h1 h2 hr hr'
  have A := pair_step hK h1 h2 hr hr'
  have B := pair_step hK h1.symm h2.symm hr' hr
  exact ⟨A.1, A.2, B.2⟩

end Formalism.L2.SG.Pf.FinXP
