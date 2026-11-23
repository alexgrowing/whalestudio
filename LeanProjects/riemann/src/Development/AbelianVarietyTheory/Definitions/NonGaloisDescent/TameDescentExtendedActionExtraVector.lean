import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

theorem act_mem_Man (g : TameGal K l e a) {v : Vec K a ι} (hv : v ∈ P.Man) : Δ.act g v ∈ P.Man :=
  Δ.act_mem_Mext g (A_le_Rpi l e) (rot_R _) hv

omit [NeZero e] in
theorem act_mem_EM (g : TameGal K l e a) {η : ℕ} {v : Vec K a ι} (hv : v ∈ P.EM η) :
    Δ.act g v ∈ P.EM η := by
  rw [mem_divE, ← act_E_pow_smul]
  exact Δ.act_mem_M g _ hv

omit [NeZero e] in
theorem act_EN (g : TameGal K l e a) (v : Vec K a ι) : Δ.act g (P.EN v) = P.EN (Δ.act g v) := by
  rw [PhiMod.EN_apply, act_E_smul, act_conn, PhiMod.EN_apply]

def actPol : Representation K (TameGal K l e a) P.Pol :=
  Δ.act.quotient P.Man fun g _ => Δ.act_mem_Man g

@[simp] theorem actPol_cls (g : TameGal K l e a) (v : Vec K a ι) :
    Δ.actPol g (P.cls v) = P.cls (Δ.act g v) := rfl

theorem actPol_Mon (g : TameGal K l e a) (y : Vec K a ι) :
    Δ.actPol g (P.Mon y) = P.Mon (Δ.act g y) := by
  rw [PhiMod.Mon_apply, actPol_cls, map_sub, act_EN, act_E_smul, act_zeta, PhiMod.Mon_apply]

theorem cls_mem_invariants {v : Vec K a ι} (hv : v ∈ Δ.inv) : P.cls v ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_cls, hv g]

theorem Mon_mem_invariants {y : Vec K a ι} (hy : y ∈ Δ.inv) : P.Mon y ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_Mon, hy g]

def invOf {B : Subalgebra O K⟦X⟧} (W : Submodule B (Vec K a ι)) : Submodule O (Vec K a ι) :=
  W.restrictScalars O ⊓ Δ.inv.restrictScalars O

omit [NeZero e] in
theorem mem_invOf {B : Subalgebra O K⟦X⟧} {W : Submodule B (Vec K a ι)} {v : Vec K a ι} :
    v ∈ Δ.invOf W ↔ v ∈ W ∧ ∀ g, Δ.act g v = v := Iff.rfl

abbrev Minv : Submodule O (Vec K a ι) := Δ.invOf P.M

abbrev Linv : Submodule O (Vec K a ι) := Δ.invOf P.L

abbrev Y (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (P.EM η)

def Y' (η : ℕ) : Submodule O (Vec K a ι) := (Δ.Y η).map ((mulV K a ι (X ^ e)).restrictScalars O)

abbrev Yl (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (divE l e η (P.Mext (invL l (A O K))))

omit [NeZero e] in
theorem mem_Y' {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Y' η ↔ ∃ y₀ ∈ Δ.Y η, (X : K⟦X⟧) ^ e • y₀ = y :=
  Iff.rfl

omit [NeZero e] in
theorem Y'_le_Y (η : ℕ) : Δ.Y' η ≤ Δ.Y η := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(P.EM η).smul_mem (uIn (A O K) ^ e) hy.1,
    fun g => (Δ.act_X_pow_smul g y).trans (congrArg _ (hy.2 g))⟩

omit [NeZero e] in
theorem mem_Yl_iff {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Yl η ↔ ∃ n : ℕ, (l : K) ^ n • y ∈ Δ.Y η := by
  have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
    simp [smul_eq_C_mul]
  constructor
  · rintro ⟨h1, h2⟩
    choose n hn using fun p : ZMod a × ι => mem_tot.1 h1 p.1 p.2
    refine ⟨Finset.univ.sup n, mem_tot.2 fun τ i => ?_, Δ.inv.smul_mem _ h2⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
    rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
  · rintro ⟨n, h1, h2⟩
    refine ⟨mem_tot.2 fun τ i => ⟨n, ?_⟩, fun g => ?_⟩
    · have := mem_tot.1 h1 τ i
      rwa [smul_comm, Pi.smul_apply, Pi.smul_apply, hl] at this
    · exact smul_right_injective _ (pow_ne_zero n (l_ne_zero l)) ((map_smul _ _ _).symm.trans (h2 g))

def Z (η : ℕ) : Submodule O P.Pol :=
  ((P.EM η).restrictScalars O).map (P.cls.restrictScalars O) ⊓ Δ.actPol.invariants.restrictScalars O

theorem mem_Z {η : ℕ} {w : P.Pol} :
    w ∈ Δ.Z η ↔ (∃ y ∈ P.EM η, P.cls y = w) ∧ ∀ g, Δ.actPol g w = w := Iff.rfl

def Zl (η : ℕ) : Submodule K P.Pol := P.PolEta η ⊓ Δ.actPol.invariants

theorem mem_Zl_of_mem_Z {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : w ∈ Δ.Zl η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := hw
  exact ⟨P.cls_mem_PolEta hy, h⟩

theorem cls_mem_Z {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ.Y η) : P.cls y ∈ Δ.Z η :=
  ⟨⟨y, hy.1, rfl⟩, Δ.cls_mem_invariants hy.2⟩

theorem vPol_mem_Z {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : P.vPol w ∈ Δ.Z η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
  refine ⟨⟨_, (P.EM η).smul_mem (uIn (A O K) ^ e) hy, rfl⟩, fun g => ?_⟩
  rw [PhiMod.vPol_cls, actPol_cls, act_X_pow_smul, ← PhiMod.vPol_cls, ← actPol_cls, h g,
    PhiMod.vPol_cls]

def actO : Representation O (TameGal K l e a) (Vec K a ι) where
  toFun g := (Δ.act g).restrictScalars O
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp

omit [NeZero e] in
@[simp] theorem actO_apply (g : TameGal K l e a) (v : Vec K a ι) : Δ.actO g v = Δ.act g v := rfl

def actEM (η : ℕ) : Representation O (TameGal K l e a) ((P.EM η).restrictScalars O) :=
  Δ.actO.subrepresentation _ fun g v hv => by
    rw [Submodule.mem_comap, actO_apply]
    exact Δ.act_mem_EM g hv

omit [NeZero e] in
theorem coe_actEM (η : ℕ) (g : TameGal K l e a) (v : (P.EM η).restrictScalars O) :
    (Δ.actEM η g v : Vec K a ι) = Δ.act g v := rfl

def actQuot (η : ℕ) : Representation O (TameGal K l e a)
    ((P.EM η).restrictScalars O ⧸ (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) :=
  (Δ.actEM η).quotient _ fun g v hv => by
    have h : Δ.act g v ∈ P.M := Δ.act_mem_M g _ hv
    rw [← coe_actEM] at h
    exact h

variable (P) in

def quotToPol (η : ℕ) : ((P.EM η).restrictScalars O ⧸
    (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) →ₗ[O] P.Pol :=
  Submodule.liftQ _ (P.cls.restrictScalars O ∘ₗ Submodule.subtype _)
    fun _ hv => P.cls_eq_zero_iff.2 (P.M_le_Man hv)

theorem quotToPol_act (η : ℕ) (g : TameGal K l e a) (w) :
    quotToPol P η (Δ.actQuot η g w) = Δ.actPol g (quotToPol P η w) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

variable [CompleteSpace K]

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem quotToPol_injective (η : ℕ) : Function.Injective (quotToPol P η) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _
    fun y hy => P.mem_M_of_mem_Man y.2 (P.cls_eq_zero_iff.1 hy))

theorem map_invariants_actQuot (η : ℕ) :
    (Δ.actQuot η).invariants.map (quotToPol P η) = Δ.Z η := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun g => by rw [← quotToPol_act, hw g]⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, fun g => quotToPol_injective η
      ((Δ.quotToPol_act η g _).trans (h g)), rfl⟩

def quotInvEquiv (η : ℕ) : (Δ.actQuot η).invariants ≃ₗ[O] Δ.Z η :=
  (Submodule.equivMapOfInjective _ (quotToPol_injective η) _).trans
    (LinearEquiv.ofEq _ _ (Δ.map_invariants_actQuot η))

end Descent

namespace Descent

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

structure Hom (Δ₁ : Descent P) (Δ₂ : Descent Q) extends BK.Hom P Q where
  app_act : ∀ g v, toHom.app (Δ₁.act g v) = Δ₂.act g (toHom.app v)

namespace Hom

variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)

variable (Δ₁) in

def scalar (c : O) : Hom Δ₁ Δ₁ where
  toHom := BK.Hom.scalar P c
  app_act g v := by
    simp only [BK.Hom.app_scalar, algebraMap_smul]
    exact (map_smul (Δ₁.actO g) c v).symm

def comp (G : Hom Δ₂ Δ₃) (F : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  toHom := G.toHom.comp F.toHom
  app_act g v := by rw [BK.Hom.app_comp, BK.Hom.app_comp, F.app_act, G.app_act]

omit [NeZero e] in
theorem app_mem_inv {v : Vec K a ι} (hv : v ∈ Δ₁.inv) : F.app v ∈ Δ₂.inv :=
  fun g => by rw [← F.app_act, hv g]

omit [NeZero e] in
theorem app_mem_Minv {v : Vec K a ι} (hv : v ∈ Δ₁.Minv) : F.app v ∈ Δ₂.Minv :=
  ⟨F.app_mem_M hv.1, F.app_mem_inv hv.2⟩

omit [NeZero e] in
theorem app_mem_Y {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y η) : F.app y ∈ Δ₂.Y η :=
  ⟨F.app_mem_EM hy.1, F.app_mem_inv hy.2⟩

omit [NeZero e] in
theorem app_mem_Y' {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y' η) : F.app y ∈ Δ₂.Y' η := by
  obtain ⟨y₀, h₀, rfl⟩ := Δ₁.mem_Y'.1 hy
  exact Δ₂.mem_Y'.2 ⟨_, F.app_mem_Y h₀, (map_smul _ _ _).symm⟩

theorem onPol_act (g : TameGal K l e a) (w : P.Pol) :
    F.onPol (Δ₁.actPol g w) = Δ₂.actPol g (F.onPol w) := by
  obtain ⟨y, rfl⟩ := P.Man.mkQ_surjective w
  rw [actPol_cls, BK.Hom.onPol_cls, BK.Hom.onPol_cls, actPol_cls, F.app_act]

theorem onPol_mem_Z {η : ℕ} {w : P.Pol} (hw : w ∈ Δ₁.Z η) : F.onPol w ∈ Δ₂.Z η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ₁.mem_Z.1 hw
  exact Δ₂.mem_Z.2 ⟨⟨_, F.app_mem_EM hy, rfl⟩, fun g => by rw [← F.onPol_act, h g]⟩

theorem onPol_mem_Zl {η : ℕ} {w : P.Pol} (hw : w ∈ Δ₁.Zl η) : F.onPol w ∈ Δ₂.Zl η :=
  ⟨F.onPol_mem_PolEta hw.1, fun g => by rw [← F.onPol_act, hw.2 g]⟩

end Hom

variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)

def plusInl : Hom Δ (Δ.plus hy hinv) where
  toHom := P.plusInl hy
  app_act g v := by rw [P.plusInl_app, P.plusInl_app, plus_act_join, map_zero]

theorem tameDescent_extended_action_extraVector (g : TameGal K l e a) : (Δ.plus hy hinv).act g xVec = xVec := by
  rw [xVec, plus_act_join, map_zero, map_one]

end Descent

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in

structure IsExactTriple {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
    (F : Hom P Q) (G : Hom Q T) : Prop where
  inj : ∀ v ∈ P.M, F.app v = 0 → v = 0
  exact : ∀ v ∈ Q.M, G.app v = 0 ↔ v ∈ F.imM
  finiteLength : IsFiniteLength (A O K) G.coker

namespace PhiMod

omit [NeZero a] [TameDescentExponentData K l e a]

variable (P : PhiMod O K l e a ι)

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem nabla_mem_MM_of_basis (h : ∀ i, P.nabla (P.phi (bas i)) ∈ P.MM)
    (h' : ∀ i, P.phi (bas i) ∈ P.MM) {m : Vec K a ι} (hm : m ∈ P.MM) : P.nabla m ∈ P.MM := by
  rw [P.eq_sum_phi_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) := P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  rw [nabla_smul_tot]
  exact add_mem (P.smul_tot_mem_ext (fun τ => derivative_mem_S (hc τ)) (h' i))
    (P.smul_tot_mem_ext hc (h i))

theorem EN_mem_Man_of_basis (h : ∀ i, P.EN (bas i) ∈ P.Man) {m : Vec K a ι} (hm : m ∈ P.Man) :
    P.EN m ∈ P.Man := by
  rw [eq_sum_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) : m τ i ∈ Rpi O K l e := mem_tot.1 hm τ i
  rw [EN_apply, conn_smul_tot, smul_add, smul_comm (E K l e) (fun τ => m τ i)]
  exact add_mem (P.smul_mem_Man (E_mem l e _) (P.smul_tot_mem_Mext
    (fun τ => N_mem (derivative_mem_R l (hc τ))) (P.M_le_Man (P.bas_mem_M i))))
    (P.smul_tot_mem_Mext hc (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [Fact l.Prime] in
theorem smul_mem_ext_of_basis {c : K⟦X⟧} (h : ∀ i, c • bas i ∈ P.L) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.Mext B) : c • m ∈ P.ext B := by
  rw [eq_sum_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_ext (fun τ => mem_tot.1 hm τ i) (P.ext_mono hB (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem smul_mem_Mext_of_basis {c : K⟦X⟧} (h : ∀ i, c • P.phi (bas i) ∈ P.M) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.ext B) : c • m ∈ P.Mext B := by
  rw [P.eq_sum_phi_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_Mext (fun τ => P.mem_extc_iff.1 (mem_tot.1 hm τ) i) (P.Mext_mono hB (h i))

variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

omit [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem bas_inl (i : ι) : bas (Sum.inl i) = (P.plusInl hy).app (bas i) := by
  rw [plusInl_app]
  ext τ (j | j) : 2 <;> simp [bas, join, Pi.single_apply]

omit [IsUltrametricDist K] [Fintype ι] in
theorem bas_inr : (bas (Sum.inr ()) : Vec K a (ι ⊕ Unit)) = xVec := by
  ext τ (j | j) : 2 <;> simp [bas, join, xVec]

theorem plus_upper {η : ℕ} (h : ∀ v ∈ P.L, E K l e ^ η • v ∈ P.M) (hη : y ∈ P.EM η) :
    ∀ v ∈ (P.plus hy).L, E K l e ^ η • v ∈ (P.plus hy).M := fun _ =>
  (P.plus hy).smul_mem_Mext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← Hom.app_phi, ← map_smul]
      exact Hom.app_mem_M _ (h _ (P.phi_mem_L (P.bas_mem_M i)))
    · rw [bas_inr, phi_extension_generator_eq_add, smul_add, ← map_smul, ← bas_inr]
      exact add_mem ((P.plus hy).M.smul_mem (EIn l e (A O K) ^ η) ((P.plus hy).bas_mem_M _))
        (Hom.app_mem_M _ hη)) le_rfl

theorem plus_lower {n : ℕ} (h : ∀ v ∈ P.M, E K l e ^ n • v ∈ P.L) (hn : E K l e ^ n • y ∈ P.L) :
    ∀ v ∈ (P.plus hy).M, E K l e ^ n • v ∈ (P.plus hy).L := fun _ =>
  (P.plus hy).smul_mem_ext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← map_smul]
      exact Hom.app_mem_ext _ le_rfl (h _ (P.bas_mem_M i))
    · rw [bas_inr, eq_sub_of_add_eq (P.phi_extension_generator_eq_add hy).symm, smul_sub,
        ← map_smul (P.plusInl hy).app, ← bas_inr]
      exact sub_mem ((P.plus hy).L.smul_mem (EIn l e (A O K) ^ n)
        ((P.plus hy).phi_mem_L ((P.plus hy).bas_mem_M _))) (Hom.app_mem_ext _ le_rfl hn)) le_rfl

theorem isExactTriple_plus [NormedAlgebra ℚ_[l] K] [NeZero e] :
    IsExactTriple (P.plusInl hy) (P.plusProj hy) where
  inj v _ h := by
    rw [plusInl_app] at h
    exact funext fun τ => funext fun i => congrFun (congrFun h τ) (.inl i)
  exact v hv := by
    rw [← join_eta v, plusProj_app]
    constructor
    · intro h
      refine ⟨fun τ i => v τ (.inl i), mem_tot.2 fun τ i => mem_tot.1 hv τ (.inl i), ?_⟩
      refine (P.plusInl_app hy _).trans (congrArg _ ?_)
      exact funext fun τ => (congrFun (congrFun h τ) ()).symm
    · rintro ⟨w, -, hw⟩
      have := (P.plusInl_app hy w).symm.trans hw
      exact funext fun τ => funext fun _ => (congrFun (congrFun this τ) (.inr ())).symm
  finiteLength := by
    have : Subsingleton (P.plusProj hy).coker := Submodule.Quotient.subsingleton_iff.2 <|
      eq_top_iff.2 fun v _ => ⟨join 0 fun τ => v.1 τ (), (P.join_mem_Mext hy).2
        ⟨zero_mem _, fun τ => mem_tot.1 v.2 τ ()⟩, P.plusProj_app hy _ _⟩
    exact .of_subsingleton

end PhiMod

end GlobalTheory.BK
