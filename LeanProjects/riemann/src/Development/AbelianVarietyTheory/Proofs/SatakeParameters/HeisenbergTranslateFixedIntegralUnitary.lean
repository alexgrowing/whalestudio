import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependentStatement

noncomputable section

namespace GlobalTheory.Hk3.HoweFix

open Formalism.UG GlobalTheory.Hk3.HoweDuality

section Glue

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem int_entry' {m : ℕ} {h : GL (Fin m) L} (hh : h ∈ GLint (Fin m) (intL L)) (i j : Fin m) :
    (h : Matrix (Fin m) (Fin m) L) i j ∈ intL L := by
  obtain ⟨k, rfl⟩ := hh; simp [Formalism.UG.bc]

theorem mul_mem_intMat' {a b : ℕ} {h : GL (Fin a) L} (hh : h ∈ GLint (Fin a) (intL L)) {u : Matrix (Fin a) (Fin b) L}
    (hu : u ∈ intMat L a b) : (h : Matrix (Fin a) (Fin a) L) * u ∈ intMat L a b := by
  rw [mem_intMat] at hu ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (int_entry' hh i k) (hu k j)

def lmulCl {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) :
    Matrix (Fin a) (Fin b) L ⧸ intMat L a b →+ Matrix (Fin a) (Fin b) L ⧸ intMat L a b :=
  QuotientAddGroup.map _ _
    { toFun := fun x => (h : Matrix (Fin a) (Fin a) L) * x, map_zero' := Matrix.mul_zero _,
      map_add' := Matrix.mul_add _ }
    (fun _ hu => mul_mem_intMat' hh hu)

theorem lmulCl_mk {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (x : Matrix (Fin a) (Fin b) L) :
    lmulCl h hh (QuotientAddGroup.mk x) = QuotientAddGroup.mk ((h : Matrix (Fin a) (Fin a) L) * x) := rfl

theorem lmulCl_mul {a b : ℕ} (h h' : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (hh' : h' ∈ GLint (Fin a) (intL L))
    (hhh : h * h' ∈ GLint (Fin a) (intL L)) (c : Matrix (Fin a) (Fin b) L ⧸ intMat L a b) :
    lmulCl (h * h') hhh c = lmulCl h hh (lmulCl h' hh' c) := by
  induction c using QuotientAddGroup.induction_on with
  | H x => simp only [lmulCl_mk, Units.val_mul, Matrix.mul_assoc]

abbrev KInt (σ : L →+* L) {a : ℕ} (J : Matrix (Fin a) (Fin a) L) : Subgroup (UJ σ J) :=
  (GLint (Fin a) (intL L)).comap (UJ σ J).subtype

def actCl (σ : L →+* L) {a b : ℕ} (J : Matrix (Fin a) (Fin a) L) :
    MulAction (KInt σ J) (Matrix (Fin a) (Fin b) L ⧸ intMat L a b) where
  smul k c := lmulCl ((k : UJ σ J) : GL (Fin a) L) (Subgroup.mem_comap.1 k.2) c
  one_smul c := by
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      show lmulCl _ _ _ = _
      simp [lmulCl]
  mul_smul k k' c :=
    lmulCl_mul (((k : UJ σ J) : GL (Fin a) L)) (((k' : UJ σ J) : GL (Fin a) L)) _ _ _ c

theorem addChar_ne_zero (ψ : AddChar L ℂ) (a : L) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end Glue

theorem eq_zero_of_mem_compl {ι M : Type} [AddCommGroup M] [Module ℂ M] {V : ι → Submodule ℂ M}
    (hV : iSupIndep V) (F : Finset ι) :
    ∀ w : M, w ∈ (⨆ i ∈ F, V i) → (∀ d, w ∈ ⨆ (j) (_ : j ≠ d), V j) → w = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => intro w hw _; simpa using hw
  | insert d F hd ih =>
    intro w hw h
    rw [Finset.iSup_insert] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    have hbP : b ∈ ⨆ (j) (_ : j ≠ d), V j := by
      refine (iSup₂_le fun j hj => ?_ : (⨆ i ∈ F, V i) ≤ _) hb
      exact le_iSup₂_of_le (f := fun j (_ : j ≠ d) => V j) j (fun e => hd (e ▸ hj)) le_rfl
    have haP : a ∈ ⨆ (j) (_ : j ≠ d), V j := by
      have := Submodule.sub_mem _ (h d) hbP
      simpa using this
    have ha0 : a = 0 := (Submodule.disjoint_def.1 (hV d)) a ha haP
    subst ha0
    simp only [zero_add] at h ⊢
    exact ih b hb h

section Data

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

theorem rho_add_int' (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (x u : Matrix (Fin n') (Fin n) L) (hu : u ∈ intMat L n' n) : ∃ c : ℂ, c ≠ 0 ∧ ρ (x + u) s = c • ρ x s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x u)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hs u ((mem_intMat u).1 hu)] at h1
  obtain ⟨c, hc, h2⟩ : ∃ c : ℂ, c ≠ 0 ∧ ρ x s = c • ρ (x + u) s := ⟨_, addChar_ne_zero ψ _, h1⟩
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem rho_mem_span_of_mk_eq (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    {x y : Matrix (Fin n') (Fin n) L}
    (hxy : (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk y) :
    ρ x s ∈ Submodule.span ℂ {ρ y s} := by
  have hu : -y + x ∈ intMat L n' n := QuotientAddGroup.eq.1 hxy.symm
  obtain ⟨c, -, hc⟩ := rho_add_int' hP hs y (-y + x) hu
  rw [add_neg_cancel_left] at hc
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem om_rho' (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (h : UJ σ (JT : Matrix (Fin n') (Fin n') L)) (hh : (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L))
    (x : Matrix (Fin n') (Fin n) L) : ω (1, h) (ρ x s) = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.norm 1 h x)
  have hfix := hP.fix 1 h (by simpa using (GLint (Fin n) (intL L)).one_mem) hh s hs
  simp only [Module.End.mul_apply] at h1
  rw [h1, hfix]
  have h1' : (((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) = 1 := by
    rw [OneMemClass.coe_one, inv_one]
  rw [h1', Units.val_one, Matrix.mul_one]

end Data

end GlobalTheory.Hk3.HoweFix

namespace GlobalTheory.Hk3

open Formalism.UG GlobalTheory.Hk3.HoweDuality GlobalTheory.Hk3.HoweFix

theorem class_fixed_phase : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ρ x s ≠ 0 ∧ ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L)) →
      ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s = ρ x s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs x hw
  obtain ⟨w, hw0, hwf, hwm⟩ := hw
  classical
  letI := actCl (b := n) σ (JT : Matrix (Fin n') (Fin n') L)
  let V : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M := fun c =>
    Submodule.span ℂ {w : M | ∃ y : Matrix (Fin n') (Fin n) L,
      (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = c ∧ w = ρ y s}
  let P : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M := fun c => ⨆ (j) (_ : j ≠ c), V j
  let π : KInt σ (JT : Matrix (Fin n') (Fin n') L) → Module.End ℂ M :=
    fun k => ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L)))
  have hind : iSupIndep V := GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs
  have hsmul : ∀ (k : KInt σ (JT : Matrix (Fin n') (Fin n') L)) (y : Matrix (Fin n') (Fin n) L),
      k • (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) =
        QuotientAddGroup.mk ((((k : UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * y) :=
    fun _ _ => rfl
  have hmemV : ∀ y, ρ y s ∈ V (QuotientAddGroup.mk y) := fun y => Submodule.subset_span ⟨y, rfl, rfl⟩
  have hVle : ∀ y, V (QuotientAddGroup.mk y) ≤ Submodule.span ℂ {ρ y s} := by
    intro y
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact rho_mem_span_of_mk_eq hP hs hz
  have hπV : ∀ k c, ∀ v ∈ V c, π k v ∈ V (k • c) := by
    intro k c v hv
    have hle : (V c).map (π k) ≤ V (k • c) := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨y, rfl, rfl⟩, rfl⟩
      show ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) (ρ y s) ∈ _
      rw [om_rho' hP hs _ (Subgroup.mem_comap.1 k.2), hsmul]
      exact hmemV _
    exact hle (Submodule.mem_map_of_mem hv)
  have hπP : ∀ k c, ∀ v ∈ P c, π k v ∈ P (k • c) := by
    intro k c v hv
    have hle : (P c).map (π k) ≤ P (k • c) := by
      simp only [P, Submodule.map_iSup]
      refine iSup₂_le fun j hj => ?_
      refine Submodule.map_le_iff_le_comap.2 fun v hv => ?_
      exact le_iSup₂_of_le (f := fun j (_ : j ≠ k • c) => V j) (k • j) (fun e => hj (smul_left_cancel k e)) le_rfl
        (hπV k j v hv)
    exact hle (Submodule.mem_map_of_mem hv)
  have hinv : ∀ (k : KInt σ (JT : Matrix (Fin n') (Fin n') L)) v, π k⁻¹ (π k v) = v := by
    intro k v
    show ω (1, ((k⁻¹ : KInt σ (JT : Matrix (Fin n') (Fin n') L)) : UJ σ (JT : Matrix (Fin n') (Fin n') L)))
      (ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) v) = v
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [Prod.mk_mul_mk, one_mul]
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, ← Prod.one_eq_mk, map_one]
    rfl
  have hfixK : ∀ k, π k w = w := fun k => hwf k (Subgroup.mem_comap.1 k.2)
  have huniq : ∀ c a b a' b', a ∈ V c → b ∈ P c → a' ∈ V c → b' ∈ P c → a + b = a' + b' → a = a' := by
    intro c a b a' b' ha hb ha' hb' he
    have h1 : a - a' ∈ V c := sub_mem ha ha'
    have h2 : a - a' ∈ P c := by
      have e : a - a' = b' - b := by rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      rw [e]; exact sub_mem hb' hb
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (hind c)) _ h1 h2)
  have hwO : w ∈ ⨆ k : KInt σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x) := by
    refine (Submodule.span_le.2 ?_) hwm
    rintro _ ⟨h, hh, rfl⟩
    refine Submodule.mem_iSup_of_mem (⟨h, hh⟩ : KInt σ (JT : Matrix (Fin n') (Fin n') L)) ?_
    rw [hsmul]
    exact hmemV _
  have hwAll : w ∈ ⨆ c, V c := (iSup_le fun k => le_iSup V _) hwO
  obtain ⟨d, hd⟩ : ∃ d, w ∉ P d := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨F, hF⟩ := (Submodule.mem_iSup_iff_exists_finset).1 hwAll
    exact hw0 (eq_zero_of_mem_compl hind F w hF hcon)
  obtain ⟨k, hk⟩ : ∃ k : KInt σ (JT : Matrix (Fin n') (Fin n') L), k • QuotientAddGroup.mk x = d := by
    by_contra hcon
    push_neg at hcon
    exact hd ((iSup_le fun k => le_iSup₂_of_le (f := fun j (_ : j ≠ d) => V j) (k • QuotientAddGroup.mk x) (hcon k) le_rfl) hwO)
  have hsplit : w ∈ V d ⊔ P d := by
    have e := iSup_split_single V d
    rw [e] at hwAll
    exact hwAll
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsplit
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_add] at hab
    exact hd (hab ▸ hb)
  have hkd : k⁻¹ • d = QuotientAddGroup.mk x := by rw [← hk, inv_smul_smul]
  have ha' : π k⁻¹ a ∈ V (QuotientAddGroup.mk x) := hkd ▸ hπV k⁻¹ d a ha
  have hb' : π k⁻¹ b ∈ P (QuotientAddGroup.mk x) := hkd ▸ hπP k⁻¹ d b hb
  have hwab' : w = π k⁻¹ a + π k⁻¹ b := by rw [← map_add, hab, hfixK]
  have ha'0 : π k⁻¹ a ≠ 0 := by
    intro e
    apply ha0
    have := hinv k⁻¹ a
    rw [inv_inv, e, map_zero] at this
    exact this.symm
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hVle x ha')
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    exact ha'0 hα.symm
  have hρ0 : ρ x s ≠ 0 := by
    intro e
    rw [e, smul_zero] at hα
    exact ha'0 hα.symm
  refine ⟨hρ0, fun h hh hhx => ?_⟩
  let kh : KInt σ (JT : Matrix (Fin n') (Fin n') L) := ⟨h, hh⟩
  have hcl : kh • (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk x := by
    rw [hsmul]
    refine QuotientAddGroup.eq.2 ?_
    have := neg_mem (show ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x ∈ intMat L n' n from hhx)
    simpa [neg_sub, sub_eq_neg_add, add_comm] using this
  have e1 : π kh (π k⁻¹ a) = π k⁻¹ a := by
    refine huniq (QuotientAddGroup.mk x) _ (π kh (π k⁻¹ b)) _ (π k⁻¹ b)
      (hcl ▸ hπV kh _ _ ha') (hcl ▸ hπP kh _ _ hb') ha' hb' ?_
    rw [← map_add, ← hwab']
    exact hfixK kh
  rw [← hα, map_smul] at e1
  have e2 : π kh (ρ x s) = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := om_rho' hP hs h hh x
  rw [e2] at e1
  exact smul_right_injective M hα0 e1

end GlobalTheory.Hk3

end
