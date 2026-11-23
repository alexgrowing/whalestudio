import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOkEig

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.L2.DIV Formalism.ConjugateSelfDual Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open GlobalTheory.ExpFrame.GLInhab (oneVec oneVec_ne_zero grp_oneVec one_mem_dualWeyl)

namespace GlobalTheory.ExpFrame.Inhab

variable (l : ℕ) [Fact l.Prime]

def embZ : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])

theorem embZ_ring : Function.Injective (embZ l) ∧ ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧
    Set.range (embZ l) = {x | x ∈ L ∧ ‖x‖ ≤ 1} := by
  refine ⟨(algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp Subtype.val_injective, ⊥, inferInstance, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨IntermediateField.mem_bot.2 ⟨(y : ℚ_[l]), rfl⟩, ?_⟩
    show ‖algebraMap ℚ_[l] (PadicAlgCl l) (y : ℚ_[l])‖ ≤ 1
    rw [norm_algebraMap']
    exact y.2
  · rintro ⟨hx, hn⟩
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
    rw [norm_algebraMap'] at hn
    exact ⟨⟨y, hn⟩, rfl⟩

def twoFrame (N : ℕ) : Frame l Unit N where
  O := ℤ_[l]
  emb := embZ l
  G := GL (Fin N) ℤ_[l] × Multiplicative (ZMod 2)
  Γ := ⊥
  K := (MonoidHom.snd _ _).ker
  kap := MonoidHom.pi fun _ => (MonoidHom.fst _ _).comp (Subgroup.subtype _)
  chi := Matrix.GeneralLinearGroup.det.comp ((MonoidHom.fst _ _).comp (Subgroup.subtype _))
  I := Unit
  tr _ := {(1, Multiplicative.ofAdd 1)}
  cst _ := 1

theorem twoFrame_ok (N : ℕ) : (twoFrame l N).Ok where
  ring := embZ_ring l
  classes := by
    classical
    refine ⟨Finset.univ.image fun a : Multiplicative (ZMod 2) => ((1 : GL (Fin N) ℤ_[l]), a), ?_⟩
    rintro ⟨g, a⟩
    refine ⟨1, Subgroup.one_mem _, (1, a), Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, (g, 1), rfl, ?_⟩
    exact Prod.ext (by change g = 1 * 1 * g; simp) (by change a = 1 * a * 1; simp)
  tame g := by
    have hu : Unique {γ : (twoFrame l N).Γ // g⁻¹ * (γ : (twoFrame l N).G) * g ∈ (twoFrame l N).K} :=
      { default := ⟨1, by simp⟩
        uniq := fun a => Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 a.1.2)) }
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_unique, Nat.dvd_one]
    exact (Fact.out : l.Prime).ne_one
  perm i κ := by
    refine ⟨1, fun s => ⟨κ, ?_, rfl, rfl⟩⟩
    obtain ⟨s, hs⟩ := s
    obtain rfl := Finset.mem_singleton.1 hs
    obtain ⟨⟨g, a⟩, h⟩ := κ
    exact Prod.ext (by change g * 1 = 1 * g; simp) (mul_comm _ _)
  comm i j := by
    refine ⟨Equiv.refl _, fun x => ?_⟩
    have e : ((((Equiv.refl _ x).1 : (twoFrame l N).tr j) : (twoFrame l N).G) * ((Equiv.refl _ x).2 : (twoFrame l N).tr i))⁻¹ *
      ((x.1 : (twoFrame l N).G) * x.2) = 1 := inv_mul_cancel _
    have h1 : (twoFrame l N).Triv 1 := ⟨Subgroup.one_mem _, map_one _, map_one _⟩
    exact (congrArg (twoFrame l N).Triv e).mpr h1

def sg (e : ℤˣ) (a : Multiplicative (ZMod 2)) : PadicAlgCl l := ((e ^ (Multiplicative.toAdd a) : ℤˣ) : ℤ)

def act (N : ℕ) (mu : Unit → ℕ → ℕ) (g : GL (Fin N) ℤ_[l]) : Module.End (PadicAlgCl l) (NablaT (PadicAlgCl l) N mu) :=
  embZ l (Matrix.GeneralLinearGroup.det g : ℤ_[l]ˣ) • grp (PadicAlgCl l) N mu fun _ => Matrix.GeneralLinearGroup.map (embZ l) g

theorem act_one (N : ℕ) (mu : Unit → ℕ → ℕ) : act l N mu 1 = 1 := by
  have e : (fun _ : Unit => Matrix.GeneralLinearGroup.map (n := Fin N) (embZ l) 1) = 1 := funext fun _ => map_one _
  have e2 : grp (PadicAlgCl l) N mu 1 = 1 := map_one _
  rw [act, e, e2, map_one, Units.val_one, map_one, one_smul]

theorem act_mul (N : ℕ) (mu : Unit → ℕ → ℕ) (g h : GL (Fin N) ℤ_[l]) : act l N mu (g * h) = act l N mu g * act l N mu h := by
  have e : (fun _ : Unit => Matrix.GeneralLinearGroup.map (n := Fin N) (embZ l) (g * h)) =
    (fun _ : Unit => Matrix.GeneralLinearGroup.map (n := Fin N) (embZ l) g) * fun _ => Matrix.GeneralLinearGroup.map (embZ l) h :=
      funext fun _ => map_mul _ _ _
  have e2 : ∀ a b, grp (PadicAlgCl l) N mu (a * b) = grp (PadicAlgCl l) N mu a * grp (PadicAlgCl l) N mu b := fun a b => map_mul _ _ _
  rw [act, e, e2, map_mul, Units.val_mul, map_mul, act, act, smul_mul_smul_comm]

theorem twoFrame_isEig (N : ℕ) (mu : Unit → ℕ → ℕ) (v : NablaT (PadicAlgCl l) N mu) (hv : v ≠ 0) (e : ℤˣ) :
    (twoFrame l N).IsEig mu fun _ => ((e : ℤ) : PadicAlgCl l) := by
  refine ⟨fun g : GL (Fin N) ℤ_[l] × Multiplicative (ZMod 2) => sg l e g.2 • act l N mu g.1⁻¹ v, fun h => hv ?_,
    ⟨fun γ hγ g => ?_, fun κ g => ?_⟩, fun i g => ?_⟩
  · have := congrFun h (1, 1)
    change sg l e 1 • act l N mu 1⁻¹ v = 0 at this
    simpa [sg, act_one] using this
  · obtain rfl := Subgroup.mem_bot.1 hγ
    exact congrArg (fun g : GL (Fin N) ℤ_[l] × Multiplicative (ZMod 2) => sg l e g.2 • act l N mu g.1⁻¹ v) (one_mul g)
  · obtain ⟨⟨k, a⟩, hk⟩ := κ
    obtain rfl : a = 1 := hk
    obtain ⟨g, b⟩ := g
    change act l N mu k (sg l e (b * 1) • act l N mu (g * k)⁻¹ v) = sg l e b • act l N mu g⁻¹ v
    rw [mul_one, map_smul, ← Module.End.mul_apply, ← act_mul, mul_inv_rev, mul_inv_cancel_left]
  · obtain ⟨g, b⟩ := g
    change embZ l 1 • ∑ s ∈ ({(1, Multiplicative.ofAdd 1)} : Finset (GL (Fin N) ℤ_[l] × Multiplicative (ZMod 2))),
      sg l e (b * s.2) • act l N mu (g * s.1)⁻¹ v = ((e : ℤ) : PadicAlgCl l) • sg l e b • act l N mu g⁻¹ v
    rw [map_one, one_smul, Finset.sum_singleton, mul_one, smul_smul]
    congr 1
    simp [sg, uzpow_add, mul_comm]

theorem twoFrame_isEig_neg (N : ℕ) : (twoFrame l N).IsEig (fun _ _ => 0) fun _ => -1 := by
  simpa using twoFrame_isEig l N _ _ (oneVec_ne_zero l N) (-1)

theorem exists_over {ι : Type} {N : ℕ} (F : Frame l ι N) (hF : F.Ok) (θ : F.I → PadicAlgCl l) (hθ : ∀ i, ‖θ i‖ ≤ 1) :
    ∃ m : Ideal F.T, m.IsPrime ∧ F.Over θ m := by
  have hle : ∀ p : F.T, ‖MvPolynomial.eval₂ F.emb θ p‖ ≤ 1 := fun p => by
    induction p using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨L, -, hL⟩ := hF.ring.2
      rw [MvPolynomial.eval₂_C]
      exact (hL ▸ Set.mem_range_self c : F.emb c ∈ {x | x ∈ L ∧ ‖x‖ ≤ 1}).2
    | add p q hp hq => rw [MvPolynomial.eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
    | mul_X p i hp => rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, norm_mul]; exact mul_le_one₀ hp (norm_nonneg _) (hθ i)
  let m : Ideal F.T :=
    { carrier := {p | ‖MvPolynomial.eval₂ F.emb θ p‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, MvPolynomial.eval₂_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MvPolynomial.eval₂_mul, norm_mul] at *
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  refine ⟨m, ⟨fun h => ?_, fun {x y} h => ?_⟩, hθ, fun p => Iff.rfl⟩
  · have : (1 : F.T) ∈ m := h ▸ Submodule.mem_top
    change ‖MvPolynomial.eval₂ F.emb θ 1‖ < 1 at this
    simp at this
  · change ‖MvPolynomial.eval₂ F.emb θ (x * y)‖ < 1 at h
    by_contra hc
    push Not at hc
    have h1 : ‖MvPolynomial.eval₂ F.emb θ x‖ = 1 := le_antisymm (hle x) (not_lt.1 hc.1)
    have h2 : ‖MvPolynomial.eval₂ F.emb θ y‖ = 1 := le_antisymm (hle y) (not_lt.1 hc.2)
    rw [MvPolynomial.eval₂_mul, norm_mul, h1, h2] at h
    simp at h

def HasLevelSetting {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) : Prop :=
  ∃ (jK : F.K →* alg F.O N lam) (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)))
    (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))) (m : Ideal F.T),
      m.IsPrime ∧ F.IsJ lam jK ∧ F.IsHecke lam jK (NablaT F.O N lam) ∧ F.Over θ m

theorem hasLevelSetting {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (hF : F.Ok) (lam : ι → ℕ → ℕ)
    (θ : F.I → PadicAlgCl l) (hθ : ∀ i, ‖θ i‖ ≤ 1) : HasLevelSetting l F lam θ := by
  obtain ⟨jK, hJ⟩ := levelMap_exists l ι N F lam
  obtain ⟨i1, i2, hH⟩ := HeckeMod.hecke_module l ι N F lam jK hF hJ (NablaT F.O N lam)
  obtain ⟨m, hm, hO⟩ := exists_over l F hF θ hθ
  exact ⟨jK, i1, i2, m, hm, hJ, hH, hO⟩

theorem twoClassFrame_hasLevelSetting (N : ℕ) (lam : Unit → ℕ → ℕ) : HasLevelSetting l (twoFrame l N) lam fun _ => -1 :=
  hasLevelSetting l _ (twoFrame_ok l N) lam _ fun _ => by simp

def plc : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal :=
    { carrier := {x | ‖algebraMap ℚ (PadicAlgCl l) (x : ℚ)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective c
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        have : ‖algebraMap ℚ (PadicAlgCl l) ((Rat.ringOfIntegersEquiv.symm n : 𝓞 ℚ) : ℚ)‖ ≤ 1 := by
          rw [eq_intCast Rat.ringOfIntegersEquiv.symm n]
          simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
        exact mul_lt_one_of_nonneg_of_lt_one_right this (norm_nonneg _) hx }
  isPrime := by
    have hle : ∀ c : 𝓞 ℚ, ‖algebraMap ℚ (PadicAlgCl l) (c : ℚ)‖ ≤ 1 := fun c => by
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective c
      rw [eq_intCast Rat.ringOfIntegersEquiv.symm n]
      simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have : (1 : 𝓞 ℚ) ∈ _ := h ▸ Submodule.mem_top
      change ‖algebraMap ℚ (PadicAlgCl l) ((1 : 𝓞 ℚ) : ℚ)‖ < 1 at this
      simp at this
    · change ‖algebraMap ℚ (PadicAlgCl l) ((x * y : 𝓞 ℚ) : ℚ)‖ < 1 at h
      by_contra hc
      push Not at hc
      have h1 : ‖algebraMap ℚ (PadicAlgCl l) (x : ℚ)‖ = 1 := le_antisymm (hle x) (not_lt.1 hc.1)
      have h2 : ‖algebraMap ℚ (PadicAlgCl l) (y : ℚ)‖ = 1 := le_antisymm (hle y) (not_lt.1 hc.2)
      simp only [map_mul, norm_mul, h1, h2] at h
      simp at h
  ne_bot := by
    intro h
    have : ((l : ℕ) : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := by
      rw [← h]
      change ‖algebraMap ℚ (PadicAlgCl l) (((l : ℕ) : 𝓞 ℚ) : ℚ)‖ < 1
      have e : algebraMap ℚ (PadicAlgCl l) (((l : ℕ) : 𝓞 ℚ) : ℚ) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [e, norm_algebraMap']
      exact Padic.norm_p_lt_one
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

def line : CSD ℚ where
  Cl := Unit
  V := ℚ
  ιV := Unit
  bV := Module.Basis.singleton Unit ℚ
  pair := LinearMap.mk₂'ₛₗ _ _ (fun a b => a * b) (fun _ _ _ => add_mul _ _ _)
    (fun c a b => by simp [mul_assoc]) (fun _ _ _ => mul_add _ _ _) (fun c a b => by simp [mul_left_comm])
  Gam := fun _ => Unit
  ρ := fun _ => 1
  Nab := fun _ => Submodule.span (𝓞 ℚ) {1}
  Del := fun _ => Submodule.span (𝓞 ℚ) {1}

def dat (ev : ℕ → ℤ) : BlockDat ℚ Unit Unit where
  S := line
  r := 1
  Pl := Unit
  pl := id
  q _ := 2
  n := 3
  t := 2
  op i := (ev i.2 : ℚ) • 1
  bl := [fun _ => 1]

def scFrame (ev : ℕ → ℤ) : Frame l Unit 3 where
  O := ℤ_[l]
  emb := embZ l
  G := GL (Fin 3) ℤ_[l]
  Γ := ⊥
  K := ⊤
  kap := MonoidHom.pi fun _ => (⊤ : Subgroup (GL (Fin 3) ℤ_[l])).subtype
  chi := 1
  I := Fin 3
  tr _ := {1}
  cst i := (ev (i + 1) : ℤ_[l])

theorem scFrame_ok (ev : ℕ → ℤ) : (scFrame l ev).Ok :=
  have h := GLInhab.ok l 3
  ⟨embZ_ring l, h.classes, h.tame, fun _ κ => h.perm () κ, fun _ _ => h.comm () ()⟩

def cc : NablaT (PadicAlgCl l) 3 (fun (_ : Unit) _ => 0) →ₗ[PadicAlgCl l] PadicAlgCl l :=
  (MvPolynomial.lcoeff (PadicAlgCl l) 0).comp ((Submodule.subtype _).comp
    (PiTensorProduct.subsingletonEquiv (R := PadicAlgCl l)
      (s := fun _ : Unit => Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) 3 3 (res 3 (fun _ : ℕ => 0))) ()).toLinearMap)

theorem cc_tprod (x : Unit → Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) 3 3 (res 3 (fun _ : ℕ => 0))) :
    cc l (PiTensorProduct.tprod _ x) = MvPolynomial.coeff 0 (x ()).1 := by
  change MvPolynomial.coeff 0 (PiTensorProduct.subsingletonEquiv (R := PadicAlgCl l)
      (s := fun _ : Unit => Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) 3 3 (res 3 (fun _ : ℕ => 0))) () (PiTensorProduct.tprod _ x)).1 = _
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod]

theorem cc_one : cc l (oneVec l 3) = 1 := by
  rw [oneVec, cc_tprod]; simp

theorem one_mem_int : (1 : MvPolynomial (Fin 3 × Fin 3) ℤ_[l]) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ_[l] 3 3 (res 3 (fun _ : ℕ => 0)) := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · have h0 : res 3 (fun _ : ℕ => 0) = 0 := rfl
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule, h0]
    exact MvPolynomial.isWeightedHomogeneous_one (R := ℤ_[l]) (Formalism.GradedWeylDivisibility.colW 3 3)
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b _
    simp

def scReads (ev : ℕ → ℤ) : Reads (scFrame l ev) (fun _ _ => 0) (dat ev) (plc l) where
  e0 := algebraMap ℚ (PadicAlgCl l)
  ix i := ((), (show Fin 3 from i) + 1)
  rd :=
    { toFun := fun f _ => algebraMap ℚ (PadicAlgCl l) (f.1 ()) • oneVec l 3
      map_add' := fun f g => funext fun _ => by
        change algebraMap ℚ (PadicAlgCl l) ((show ℚ from f.1 ()) + (show ℚ from g.1 ())) • oneVec l 3 = _
        rw [map_add, add_smul]; rfl
      map_smul' := fun c f => funext fun _ => by
        change algebraMap ℚ (PadicAlgCl l) (c * (show ℚ from f.1 ())) • oneVec l 3 = _
        rw [map_mul, mul_smul]; rfl }
  place x := Iff.rfl
  range x := by
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    rw [eq_intCast Rat.ringOfIntegersEquiv.symm n]
    exact ⟨(n : ℤ_[l]), (map_intCast (embZ l) n).trans (by simp)⟩
  form f := by
    refine ⟨fun _ _ _ => rfl, fun κ g => ?_⟩
    have e3 : (scFrame l ev).emb ((scFrame l ev).chi κ) = 1 := map_one (embZ l)
    rw [e3, one_smul]
    change grp (PadicAlgCl l) 3 (fun (_ : Unit) _ => 0) _ (algebraMap ℚ (PadicAlgCl l) (f.1 ()) • oneVec l 3) =
      algebraMap ℚ (PadicAlgCl l) (f.1 ()) • oneVec l 3
    rw [map_smul, grp_oneVec]
  indep n f hf := by
    have h1 : n ≤ 1 := by
      have := (hf.map' (Submodule.subtype _) (Submodule.ker_subtype _)).fintype_card_le_finrank
      have e : Module.finrank ℚ (Unit → ℚ) = 1 := by simp
      rw [Fintype.card_fin] at this
      exact this.trans e.le
    haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 h1
    rw [linearIndependent_subsingleton_index_iff]
    intro a h0
    have h2 := congrArg (cc l) (congrFun h0 (1 : GL (Fin 3) ℤ_[l]))
    change cc l (algebraMap ℚ (PadicAlgCl l) ((f a).1 ()) • oneVec l 3) = cc l 0 at h2
    rw [map_smul, cc_one, smul_eq_mul, mul_one, map_zero] at h2
    have h3 := (map_eq_zero (algebraMap ℚ (PadicAlgCl l))).1 h2
    exact hf.ne_zero a (Subtype.ext (funext fun _ => h3))
  hecke i f g := by
    change algebraMap ℚ (PadicAlgCl l) ((ev ((show Fin 3 from i) + 1) : ℚ) * (show ℚ from f.1 ())) • oneVec l 3 =
      embZ l (ev ((show Fin 3 from i) + 1) : ℤ_[l]) • ∑ s ∈ ({1} : Finset (GL (Fin 3) ℤ_[l])), algebraMap ℚ (PadicAlgCl l) (f.1 ()) • oneVec l 3
    rw [Finset.sum_singleton, map_mul, mul_smul, map_intCast, map_intCast]
  nab f hf g := by
    have hf' : (show ℚ from f.1 ()) ∈ Submodule.span (𝓞 ℚ) {(1 : ℚ)} := hf ()
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hf'
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective c
    rw [eq_intCast Rat.ringOfIntegersEquiv.symm n] at hc
    refine AddSubgroup.subset_closure ⟨(n : ℤ_[l]), fun _ => ⟨1, one_mem_dualWeyl l 3⟩, fun τ => ⟨_, one_mem_int l, map_one _⟩, ?_⟩
    change algebraMap ℚ (PadicAlgCl l) (f.1 ()) • oneVec l 3 = embZ l (n : ℤ_[l]) • oneVec l 3
    have : (show ℚ from f.1 ()) = (n : ℚ) := by
      have h2 : ((n : 𝓞 ℚ) • (1 : ℚ)) = (n : ℚ) := by rw [Int.cast_smul_eq_zsmul]; simp
      exact hc.symm.trans h2
    rw [map_intCast, ← map_intCast (algebraMap ℚ (PadicAlgCl l)), ← this]
  del f hf := by
    have hn : ∀ c : ℤ_[l], ‖embZ l c‖ ≤ 1 := fun c => by
      change ‖algebraMap ℚ_[l] (PadicAlgCl l) (c : ℚ_[l])‖ ≤ 1
      rw [norm_algebraMap']
      exact c.2
    have key : ∀ y ∈ (scFrame l ev).latD (fun _ _ => 0), ‖cc l y‖ ≤ 1 := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, x, hx, rfl⟩ := hy
        obtain ⟨x0, -, hx0⟩ := hx ()
        rw [map_smul, cc_tprod, smul_eq_mul, ← hx0, MvPolynomial.coeff_map, norm_mul]
        exact mul_le_one₀ (hn c) (norm_nonneg _) (hn _)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      | neg a _ ha => rwa [map_neg, norm_neg]
    have h := key _ (hf (1 : GL (Fin 3) ℤ_[l]))
    set q : ℚ := f.1 () with hq
    change ‖cc l (algebraMap ℚ (PadicAlgCl l) q • oneVec l 3)‖ ≤ 1 at h
    rw [map_smul, cc_one, smul_eq_mul, mul_one] at h
    have e : ∀ a : ℚ, ‖algebraMap ℚ (PadicAlgCl l) a‖ = ‖(a : ℚ_[l])‖ := fun a => by
      rw [← norm_algebraMap' (PadicAlgCl l) (a : ℚ_[l])]; simp
    rw [e] at h
    refine ⟨((q.den : ℕ) : 𝓞 ℚ), ?_, fun c => ?_⟩
    · change ¬ ‖algebraMap ℚ (PadicAlgCl l) (((q.den : ℕ) : 𝓞 ℚ) : ℚ)‖ < 1
      rw [e]
      have := PadicInt.norm_natCast_eq_one_iff (p := l) (n := q.den)
      have hu := PadicInt.isUnit_den q h
      rw [PadicInt.isUnit_iff, PadicInt.norm_def] at hu
      simp only [map_natCast, Rat.cast_natCast]
      simp only [PadicInt.coe_natCast] at hu
      rw [hu]; exact lt_irrefl _
    · change ((q.den : ℕ) : 𝓞 ℚ) • q ∈ Submodule.span (𝓞 ℚ) {(1 : ℚ)}
      refine Submodule.mem_span_singleton.2 ⟨(q.num : 𝓞 ℚ), ?_⟩
      rw [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul]
      simp [mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

def th (ev : ℕ → ℤ) : (scFrame l ev).I → PadicAlgCl l := fun i => (ev ((show Fin 3 from i) + 1) : PadicAlgCl l)

theorem th_occurs (ev : ℕ → ℤ) : (scReads l ev).Occurs ⊤ (th l ev) := by
  let f : (dat ev).S.Forms := ⟨fun _ => (1 : ℚ), fun _ _ => rfl⟩
  refine ⟨(scReads l ev).rd f, Submodule.subset_span ⟨f, trivial, rfl⟩, fun h0 => ?_, (scReads l ev).form f, fun i g => ?_⟩
  · have h2 := congrArg (cc l) (congrFun h0 (1 : GL (Fin 3) ℤ_[l]))
    change cc l (algebraMap ℚ (PadicAlgCl l) 1 • oneVec l 3) = cc l 0 at h2
    rw [map_smul, cc_one, smul_eq_mul, mul_one, map_zero, map_one] at h2
    exact one_ne_zero h2
  · change embZ l (ev ((show Fin 3 from i) + 1) : ℤ_[l]) • ∑ s ∈ ({1} : Finset (GL (Fin 3) ℤ_[l])), algebraMap ℚ (PadicAlgCl l) 1 • oneVec l 3 =
      (ev ((show Fin 3 from i) + 1) : PadicAlgCl l) • algebraMap ℚ (PadicAlgCl l) 1 • oneVec l 3
    rw [Finset.sum_singleton, map_intCast]

def evYes : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | 2 => 7
  | 3 => 1
  | _ => 0

def evNo : ℕ → ℤ
  | 0 => 1
  | 1 => 10
  | 2 => 8
  | 3 => 1
  | _ => 0

open Polynomial in

theorem hasBlock_yes : (scReads l evYes).HasBlock (th l evYes) := by
  refine ⟨fun i => (evYes i.2 : ℚ), fun _ => by simp [evYes], fun P => ⟨1 - C 4 * X, ?_⟩, fun i => (map_intCast _ _).symm⟩
  change Formalism.L2.Col.heckePolyOf 3 2 (fun k => (evYes k : ℚ)) =
    (([fun _ : Unit => (1 : ℚ)].map fun ν => Formalism.L2.Col.blockPoly (ν P) 2 2).prod) * (1 - C 4 * X)
  simp only [Formalism.L2.Col.heckePolyOf, Formalism.L2.Col.blockPoly, Finset.sum_range_succ, Finset.prod_range_succ, evYes, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil]
  norm_num
  simp only [map_ofNat]
  ring

open Polynomial in

theorem root_of_hasBlock (ev : ℕ → ℤ) (θ : Fin 3 → PadicAlgCl l) (h : (scReads l ev).HasBlock θ) :
    1 - θ 0 + 2 * θ 1 - 8 * θ 2 = 0 := by
  have h0 : ([fun _ : Unit => (1 : ℚ)].map fun ν => Formalism.L2.Col.blockPoly (algebraMap ℚ (PadicAlgCl l) (ν ())) 2 2).prod ∣
      Formalism.L2.Col.heckePolyOf 3 2 (sysOf (Pl := Unit) (I := Fin 3) 3 (fun _ k => k) θ ()) :=
    h.dvd (Pl := Unit) (fun _ k => k) () () fun _ => rfl
  have h1 := eval_dvd (x := (1 : PadicAlgCl l)) h0
  simp [Formalism.L2.Col.heckePolyOf, Formalism.L2.Col.blockPoly, Finset.sum_range_succ, Finset.prod_range_succ, sysOf] at h1
  linear_combination h1

theorem not_hasBlock_no : ¬ (scReads l evNo).HasBlock (th l evNo) := fun h => by
  have := root_of_hasBlock l evNo _ h
  simp [th, evNo] at this
  norm_num at this

theorem not_hasBlock_zero (ev : ℕ → ℤ) : ¬ (scReads l ev).HasBlock 0 := fun h => by
  have : (1 : PadicAlgCl l) - 0 + 2 * 0 - 8 * 0 = 0 := root_of_hasBlock l ev _ h
  simp at this

def allPlaces (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] : FrobNorm E Ω l (HeightOneSpectrum (𝓞 E)) where
  lab := id
  sgn := -1
  tw := 1
  cont := continuous_const
  cofin := by simp

theorem allPlaces_reads (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] :
    (allPlaces l E Ω).Reads 1 (fun _ _ => 1) fun _ => Polynomial.X - Polynomial.C 1 := by
  intro P B σ _ _
  have e : (Polynomial.X - Polynomial.C (1 : PadicAlgCl l)).reverse = 1 - Polynomial.X := by
    rw [Polynomial.reverse, Polynomial.natDegree_X_sub_C, Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C]
    simp
  refine e.trans ?_
  simp [Formalism.L2.Col.heckePolyOf, Finset.sum_range_succ, allPlaces, sub_eq_add_neg]

end GlobalTheory.ExpFrame.Inhab

end
