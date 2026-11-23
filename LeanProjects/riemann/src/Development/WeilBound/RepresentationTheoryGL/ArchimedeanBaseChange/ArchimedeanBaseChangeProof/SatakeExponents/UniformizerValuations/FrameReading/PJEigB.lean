import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PairDoubleCosetFiniteSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.RunFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdIrrEquivOfOrdered
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.JB

section Gen

variable {Γ V W : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eqv_apply {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (g : Γ) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v

theorem fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) (v : V) :
    v ∈ GlobalTheory.PRep.fixed ρ K → φ.toLinearEquiv v ∈ GlobalTheory.PRep.fixed σ K := by
  intro hv
  rw [mem_fixed_iff'] at hv ⊢
  intro k hk
  rw [← eqv_apply, hv k hk]

theorem map_fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) :
    (GlobalTheory.PRep.fixed ρ K).map (φ.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.fixed σ K := by
  ext x
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have := fixed_eqv φ K _ h
    rwa [LinearEquiv.apply_symm_apply] at this
  · intro h
    have := fixed_eqv φ.symm K _ h
    exact this

theorem finrank_fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) :
    Module.finrank ℂ (GlobalTheory.PRep.fixed ρ K) = Module.finrank ℂ (GlobalTheory.PRep.fixed σ K) :=
  (LinearEquiv.ofSubmodules φ.toLinearEquiv _ _ (map_fixed_eqv φ K)).finrank_eq

theorem hkG_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  rw [hsum_eq ρ K f hfin.coe_toFinset.ge, hsum_eq σ K f hfin.coe_toFinset.ge, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, eqv_apply]

end Gen

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def JE (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

theorem je_eqv (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GLw a w × GLw b w) V}
    {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) :
    JE w ϖ ρ ξa ξb → JE w ϖ σ ξa ξb := by
  rintro ⟨v, hv, hne, hev⟩
  refine ⟨φ.toLinearEquiv v, fixed_eqv φ _ v hv, fun h0 => hne (φ.toLinearEquiv.map_eq_zero_iff.1 h0),
    fun x y hx hy => ?_⟩
  rw [← hkG_eqv φ _ _ (pair_double_coset_finite_support w ϖ x y), hev x y hx hy, map_smul]

theorem dl_add {N : ℕ} (w : Pl E) (x x' : Fin N → ℤ) : dl w (x + x') = dl w x * dl w x' := by
  unfold dl
  rw [← zpow_add₀ (qh_ne w)]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pw_add {N : ℕ} (ξ : Fin N → ℂˣ) (x x' : Fin N → ℤ) : pw ξ (x + x') = pw ξ x * pw ξ x' := by
  unfold pw
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem pair_eigenvalue_add (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x x' : Fin a → ℤ) (y y' : Fin b → ℤ) :
    ev2 w ξa ξb (x + x') (y + y') = ev2 w ξa ξb x y * ev2 w ξa ξb x' y' := by
  unfold ev2
  rw [dl_add, dl_add, pw_add, pw_add]
  ring

theorem dl_ne {N : ℕ} (w : Pl E) (x : Fin N → ℤ) : dl w x ≠ 0 := zpow_ne_zero _ (qh_ne w)

theorem pw_ne {N : ℕ} (ξ : Fin N → ℂˣ) (x : Fin N → ℤ) : pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem pair_eigenvalue_ne_zero (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    ev2 w ξa ξb x y ≠ 0 :=
  mul_ne_zero (mul_ne_zero (dl_ne w x) (pw_ne ξa x)) (mul_ne_zero (dl_ne w y) (pw_ne ξb y))

theorem dl_zero {N : ℕ} (w : Pl E) : dl w (0 : Fin N → ℤ) = 1 := by
  unfold dl
  simp

theorem pw_zero {N : ℕ} (ξ : Fin N → ℂˣ) : pw ξ 0 = 1 := by
  unfold pw
  simp

theorem pw_single {N : ℕ} (ξ : Fin N → ℂˣ) (i : Fin N) : pw ξ (Pi.single i 1) = ξ i := by
  unfold pw
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

def x0 (N : ℕ) : Fin N → ℤ := fun i => -(2 * ((i : ℕ) : ℤ))

theorem gap_base (N : ℕ) : Gap (x0 N) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  simp only [x0]
  omega

theorem gap_base_add_single {N : ℕ} (i : Fin N) : Gap (x0 N + Pi.single i 1) := by
  intro i' j' h
  have h' : (i' : ℕ) < j' := h
  simp only [Pi.add_apply, x0, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> subst_vars <;> omega

def probe (w : Pl E) (p : (Fin a → ℂˣ) × (Fin b → ℂˣ)) : Option (Fin a ⊕ Fin b) → ℂ
  | none => ev2 w p.1 p.2 (x0 a) (x0 b)
  | some (Sum.inl i) => ev2 w p.1 p.2 (x0 a + Pi.single i 1) (x0 b)
  | some (Sum.inr j) => ev2 w p.1 p.2 (x0 a) (x0 b + Pi.single j 1)

theorem probe_inj (w : Pl E) : Function.Injective (probe (a := a) (b := b) w) := by
  intro p p' h
  have h0 := congrFun h none
  simp only [probe] at h0
  have ha : ∀ i, ev2 w p.1 p.2 (Pi.single i 1) 0 = ev2 w p'.1 p'.2 (Pi.single i 1) 0 := by
    intro i
    have hi := congrFun h (some (Sum.inl i))
    simp only [probe] at hi
    have e1 := pair_eigenvalue_add w p.1 p.2 (x0 a) (Pi.single i 1) (x0 b) 0
    have e2 := pair_eigenvalue_add w p'.1 p'.2 (x0 a) (Pi.single i 1) (x0 b) 0
    rw [add_zero] at e1 e2
    rw [e1, e2, h0] at hi
    exact mul_left_cancel₀ (pair_eigenvalue_ne_zero w _ _ _ _) hi
  have hb : ∀ j, ev2 w p.1 p.2 0 (Pi.single j 1) = ev2 w p'.1 p'.2 0 (Pi.single j 1) := by
    intro j
    have hj := congrFun h (some (Sum.inr j))
    simp only [probe] at hj
    have e1 := pair_eigenvalue_add w p.1 p.2 (x0 a) 0 (x0 b) (Pi.single j 1)
    have e2 := pair_eigenvalue_add w p'.1 p'.2 (x0 a) 0 (x0 b) (Pi.single j 1)
    rw [add_zero] at e1 e2
    rw [e1, e2, h0] at hj
    exact mul_left_cancel₀ (pair_eigenvalue_ne_zero w _ _ _ _) hj
  refine Prod.ext (funext fun i => Units.ext ?_) (funext fun j => Units.ext ?_)
  · have := ha i
    simp only [ev2, dl_zero, pw_zero, pw_single, mul_one] at this
    exact mul_left_cancel₀ (dl_ne w _) this
  · have := hb j
    simp only [ev2, dl_zero, pw_zero, pw_single, one_mul] at this
    exact mul_left_cancel₀ (dl_ne w _) this

theorem je_finite (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLw a w × GLw b w) V) [FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w))] :
    {p : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JE w ϖ ρ p.1 p.2}.Finite := by
  let pt : Option (Fin a ⊕ Fin b) → (Fin a → ℤ) × (Fin b → ℤ)
    | none => (x0 a, x0 b)
    | some (Sum.inl i) => (x0 a + Pi.single i 1, x0 b)
    | some (Sum.inr j) => (x0 a, x0 b + Pi.single j 1)
  have hpt : ∀ (o : Option (Fin a ⊕ Fin b)) (p : (Fin a → ℂˣ) × (Fin b → ℂˣ)),
      probe w p o = ev2 w p.1 p.2 (pt o).1 (pt o).2 := by
    intro o p
    rcases o with _ | i | j <;> rfl
  have hgap : ∀ o, Gap (pt o).1 ∧ Gap (pt o).2 := by
    intro o
    rcases o with _ | i | j
    · exact ⟨gap_base a, gap_base b⟩
    · exact ⟨gap_base_add_single i, gap_base b⟩
    · exact ⟨gap_base a, gap_base_add_single j⟩
  let T : Option (Fin a ⊕ Fin b) → Module.End ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w)) := fun o =>
    hkW ρ (I2 a b w) (dc2 w ϖ (pt o).1 (pt o).2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)
  refine Set.Finite.of_finite_image (f := probe w) ?_ (probe_inj w).injOn
  refine (Set.Finite.pi (t := fun o => {μ | (T o).HasEigenvalue μ})
    fun o => Module.End.finite_hasEigenvalue (T o)).subset ?_
  rintro _ ⟨p, ⟨v, hv, hne, hev⟩, rfl⟩ o _
  show (T o).HasEigenvalue (probe w p o)
  rw [hpt o p]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hv⟩) ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_smul]
    show ((hkW ρ (I2 a b w) _ _ _ ⟨v, hv⟩ : GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) = _
    rw [hkW_apply]
    exact hev _ _ (hgap o).1 (hgap o).2
  · intro h0
    exact hne (congrArg Subtype.val h0)

end Place

section Cls

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fd_pair (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)) := by
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  exact GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ (lp Pa w) (lp Pb w) (iwGL a w) (iwGL b w)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pa.h (fun i => Pa.σ i w)).2 _ (hIa 1).2.1 (hIa 1).2.2.1)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pb.h (fun i => Pb.σ i w)).2 _ (hIb 1).2.1 (hIb 1).2.2.1)

def key {n : ℕ} (P₀ : Pre E n) (w : Pl E) (P : Pre E n) : Fin P₀.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E) :=
  if h : P₀.c = P.c then fun j => P.cls (Fin.cast h j) w else fun j => P₀.cls j w

theorem c_eq {n : ℕ} {P₀ P : Pre E n} (hP : PreEquiv P₀ P) : P₀.c = P.c := by
  obtain ⟨e, -, -⟩ := hP
  simpa using Fintype.card_congr e

theorem lp_equiv_cast {n : ℕ} (P : Pre E n) (w : Pl E) {c₀ : ℕ} (h : c₀ = P.c) :
    ∃ e : (Σ j : Fin c₀, Fin (P.cls (Fin.cast h j) w).1) ≃ Fin n,
      Nonempty ((lp P w).Equiv (GlobalTheory.SmGL.multiProd e fun j => (P.cls (Fin.cast h j) w).rep)) := by
  subst h
  exact ⟨GlobalTheory.SmGL.stdBlocks P.N P.h, ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i =>
    GlobalTheory.LocGL.IrrGL.equivOf (P.σ i w).ρ (P.σ i w).smooth (P.σ i w).irred⟩⟩

theorem key_mem {n : ℕ} (P₀ P : Pre E n) (w : Pl E) (hP : PreEquiv P₀ P) :
    key P₀ w P ∈ Set.univ.pi (fun _ => Set.range fun i => P₀.cls i w) := by
  have hc := c_eq hP
  obtain ⟨e, he, -⟩ := hP
  intro j _
  simp only [key, dif_pos hc]
  exact ⟨e.symm (Fin.cast hc j), by show P₀.cls _ w = _; rw [he, Equiv.apply_symm_apply]⟩

theorem key_eqv {n : ℕ} (P₀ P Q : Pre E n) (w : Pl E) (hP : P₀.c = P.c) (hQ : P₀.c = Q.c)
    (hk : key P₀ w P = key P₀ w Q) : Nonempty ((lp P w).Equiv (lp Q w)) := by
  simp only [key, dif_pos hP, dif_pos hQ] at hk
  obtain ⟨e1, ⟨φ1⟩⟩ := lp_equiv_cast P w hP
  obtain ⟨e2, ⟨φ2⟩⟩ := lp_equiv_cast Q w hQ
  obtain ⟨ψ⟩ := GlobalTheory.CompanionTheory.SegReorder.famCongr (f := fun j => P.cls (Fin.cast hP j) w)
    (g := fun j => Q.cls (Fin.cast hQ j) w) (fun j => congrFun hk j) e1 e2
  exact ⟨(φ1.trans ψ).trans φ2.symm⟩

def Good (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)))
    (p : Pre E a × Pre E b) : Prop :=
  PreEquiv Pa p.1 ∧ PreEquiv Pb p.2 ∧ key Pa w p.1 = κ.1 ∧ key Pb w p.2 = κ.2

def ZS (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E))) :
    Set ((Fin a → ℂˣ) × (Fin b → ℂˣ)) :=
  if h : ∃ p, Good Pa Pb w κ p then {ξ | JEig h.choose.1 h.choose.2 w ϖ ξ.1 ξ.2} else ∅

def fr (w : Pl E) (p : Pre E a × Pre E b) : ℕ := Module.finrank ℂ (GlobalTheory.PRep.fixed (pairAt p.1 p.2 w) (I2 a b w))

def MS (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E))) : ℕ :=
  if h : ∃ p, Good Pa Pb w κ p then fr w h.choose else 0

theorem zs_finite (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E))) :
    (ZS Pa Pb w ϖ κ).Finite := by
  unfold ZS
  split_ifs with h
  · have := fd_pair h.choose.1 h.choose.2 w
    exact je_finite w ϖ (pairAt h.choose.1 h.choose.2 w)
  · exact Set.finite_empty

theorem pair_eqv (Pa Qa : Pre E a) (Pb Qb : Pre E b) (w : Pl E) (φa : (lp Pa w).Equiv (lp Qa w))
    (φb : (lp Pb w).Equiv (lp Qb w)) : Nonempty ((pairAt Pa Pb w).Equiv (pairAt Qa Qb w)) :=
  ⟨GlobalTheory.SmGL.RowOneCell.extTensorEquiv φa φb⟩

theorem step (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (Pa' Qa : Pre E a) (Pb' Qb : Pre E b)
    (ha : PreEquiv Pa Pa') (hb : PreEquiv Pb Pb') (hqa : PreEquiv Pa Qa) (hqb : PreEquiv Pb Qb)
    (hka : key Pa w Qa = key Pa w Pa') (hkb : key Pb w Qb = key Pb w Pb') :
    fr w (Pa', Pb') = fr w (Qa, Qb) ∧
      ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → JEig Qa Qb w ϖ ξa ξb := by
  have ea : Nonempty ((lp Pa' w).Equiv (lp Qa w)) := key_eqv Pa Pa' Qa w (c_eq ha) (c_eq hqa) hka.symm
  have eb : Nonempty ((lp Pb' w).Equiv (lp Qb w)) := key_eqv Pb Pb' Qb w (c_eq hb) (c_eq hqb) hkb.symm
  have e : Nonempty ((pairAt Pa' Pb' w).Equiv (pairAt Qa Qb w)) := pair_eqv Pa' Qa Pb' Qb w ea.some eb.some
  exact ⟨finrank_fixed_eqv e.some _, fun ξa ξb hJ => je_eqv w ϖ e.some ξa ξb hJ⟩

theorem mem_zs (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)))
    (h : ∃ p, Good Pa Pb w κ p) (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ)) (hJ : JEig h.choose.1 h.choose.2 w ϖ ξ.1 ξ.2) :
    ξ ∈ ZS Pa Pb w ϖ κ := by
  unfold ZS
  rw [dif_pos h]
  exact hJ

theorem ms_eq (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)))
    (h : ∃ p, Good Pa Pb w κ p) : MS Pa Pb w κ = fr w h.choose :=
  dif_pos h

theorem jEigFin_at (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa' : Pre E a) (Pb' : Pre E b),
      PreEquiv Pa Pa' → PreEquiv Pb Pb' →
      Module.finrank ℂ (GlobalTheory.PRep.fixed (pairAt Pa' Pb' w) (I2 a b w)) ≤ m ∧
        ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  let KS : Set ((Fin Pa.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (w.adicCompletion E))) :=
    (Set.univ.pi fun _ => Set.range fun i => Pa.cls i w) ×ˢ (Set.univ.pi fun _ => Set.range fun i => Pb.cls i w)
  have hKS : KS.Finite :=
    (Set.Finite.pi fun _ => Set.finite_range _).prod (Set.Finite.pi fun _ => Set.finite_range _)
  refine ⟨⋃ κ ∈ KS, ZS Pa Pb w ϖ κ, ∑ κ ∈ hKS.toFinset, MS Pa Pb w κ,
    hKS.biUnion fun κ _ => zs_finite Pa Pb w ϖ κ, fun Pa' Pb' ha hb => ?_⟩
  have hκS : (key Pa w Pa', key Pb w Pb') ∈ KS := ⟨key_mem Pa Pa' w ha, key_mem Pb Pb' w hb⟩
  have h : ∃ p, Good Pa Pb w (key Pa w Pa', key Pb w Pb') p := ⟨(Pa', Pb'), ha, hb, rfl, rfl⟩
  have hG : Good Pa Pb w (key Pa w Pa', key Pb w Pb') h.choose := h.choose_spec
  have hs := step Pa Pb w ϖ Pa' h.choose.1 Pb' h.choose.2 ha hb hG.1 hG.2.1 hG.2.2.1 hG.2.2.2
  exact ⟨show fr w (Pa', Pb') ≤ _ from (hs.1.trans (ms_eq Pa Pb w _ h).symm).trans_le
      (Finset.single_le_sum (f := MS Pa Pb w) (fun _ _ => Nat.zero_le _) (hKS.mem_toFinset.2 hκS)),
    fun ξa ξb hJ => Set.mem_biUnion hκS (mem_zs Pa Pb w ϖ _ h (ξa, ξb) (hs.2 ξa ξb hJ))⟩

end Cls

theorem jEigFin : JEigFin := fun _ _ _ _ _ _ Pa Pb w ϖ _ => jEigFin_at Pa Pb w ϖ

end PositivityTheory.Rg.BcB.F.Tail.JB
