import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

section Forms

variable (k n) in

abbrev Form (M : Type*) : Type _ := Pair k n → M

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def sumOp (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) : Module.End ℂ (Form k n M) where
  toFun φ P := ∑ Q ∈ S P, w P Q • φ Q
  map_add' φ φ' := by
    ext P
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    ext P
    simp [Finset.smul_sum, smul_comm c]

def dia : 𝓀[k]ˣ →* Module.End ℂ (Form k n M) where
  toFun c := LinearMap.funLeft ℂ M fun P => c • P
  map_one' := by
    ext φ P
    simp
  map_mul' c d := by
    ext φ P
    simp [mul_comm c d, mul_smul]

@[simp] theorem dia_apply (c : 𝓀[k]ˣ) (φ : Form k n M) (P : Pair k n) : dia c φ P = φ (c • P) := rfl

def Nm : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, dia c

variable (k n M) in

def Mram : Submodule ℂ (Form k n M) := LinearMap.ker Nm

def trLat (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withLat L, LinearMap.proj P

def trKer (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withKer L, LinearMap.proj P

def tr : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trLat P.lat

def tr' : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trKer P.ker

open Classical in

def Da (q : Unif k) (a : 𝓀[k]) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => (withLat P₁.ker).filter fun P => cross q P₁ P = a) fun _ _ => 1

def D (q : Unif k) : Module.End ℂ (Form k n M) := Da q 1

open Classical in

def U (q : Unif k) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => (withKer P.lat).filter fun P₁ => cross q P₁ P = 1) fun _ _ => 1

def Gs (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ c • dia c

def GsStar (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • dia c⁻¹

def FF (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => withLat P₁.ker) fun P₁ P => χ (cross q P₁ P)

def FFStar (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => withKer P.lat) fun P P₁ => χ (-cross q P₁ P)

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem sumOp_apply (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (P : Pair k n) :
    sumOp S w φ P = ∑ Q ∈ S P, w P Q • φ Q := rfl

theorem Nm_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) : Nm φ P = ∑ c : 𝓀[k]ˣ, φ (c • P) := by
  simp only [Nm, LinearMap.sum_apply, Finset.sum_apply, dia_apply]
  congr!

theorem mem_Mram [Fintype 𝓀[k]ˣ] : φ ∈ Mram k n M ↔ ∀ P, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := by
  simp only [Mram, LinearMap.mem_ker, funext_iff, Nm_apply, Pi.zero_apply]

theorem Gs_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) : Gs χ φ P = ∑ c : 𝓀[k]ˣ, χ c • φ (c • P) := by
  simp only [Gs, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, dia_apply]
  congr!

theorem GsStar_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) :
    GsStar χ φ P = ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • φ (c⁻¹ • P) := by
  simp only [GsStar, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, dia_apply]
  congr!

theorem trLat_apply (L : Submodule 𝒪[k] (n → k)) : trLat L φ = ∑ P ∈ withLat L, φ P := by simp [trLat]

theorem trKer_apply (L : Submodule 𝒪[k] (n → k)) : trKer L φ = ∑ P ∈ withKer L, φ P := by simp [trKer]

theorem tr_apply (P : Pair k n) : tr φ P = ∑ Q ∈ withLat P.lat, φ Q := trLat_apply φ _

theorem tr'_apply (P : Pair k n) : tr' φ P = ∑ Q ∈ withKer P.ker, φ Q := trKer_apply φ _

open Classical in

theorem Da_apply (a : 𝓀[k]) (P₁ : Pair k n) :
    Da q a φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = a, φ P := by simp [Da, sumOp_apply]

open Classical in

theorem D_apply (P₁ : Pair k n) : D q φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, φ P := Da_apply q φ 1 P₁

open Classical in

theorem U_apply (P : Pair k n) : U q φ P = ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 1, φ P₁ := by
  simp [U, sumOp_apply]

theorem FF_apply (P₁ : Pair k n) : FF q χ φ P₁ = ∑ P ∈ withLat P₁.ker, χ (cross q P₁ P) • φ P := rfl

theorem FFStar_apply (P : Pair k n) : FFStar q χ φ P = ∑ P₁ ∈ withKer P.lat, χ (-cross q P₁ P) • φ P₁ := rfl

section Formulas
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]

theorem FF_up [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (x : {x : Red L // x ≠ 0}) :
    FF q χ φ (up L q x) = ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, χ (f.1 x.1) • φ (ofDual L f) := by
  simp only [FF_apply, up_ker, sum_withLat, cross_up_ofDual]

theorem FFStar_ofDual [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    FFStar q χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L q x) := by
  simp only [FFStar_apply, ofDual_lat, sum_withKer L q, cross_up_ofDual]

end Formulas

def cntIp (φ φ' : Form k n ℂ) : ℂ := ∑ᶠ P, φ P * (starRingEnd ℂ) (φ' P)

def IsAdj (A B : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ φ' : Form k n ℂ, (Function.support φ).Finite → (Function.support φ').Finite → cntIp (A φ) φ' = cntIp φ (B φ')

theorem dia_sub_mem_Mram (c : 𝓀[k]ˣ) : dia c φ - φ ∈ Mram k n M := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine (mem_Mram _).2 fun P => ?_
  simp only [Pi.sub_apply, dia_apply, Finset.sum_sub_distrib, smul_smul, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.mulLeft c) fun d => φ (d • P)

theorem dia_smul_eq_iff {c : 𝓀[k]ˣ} {P : Pair k n} : c • P = P ↔ c = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := Pair.dia_hasVal.1 (h.symm ▸ P.hasVal_vec : (c • P).HasVal P.vec 1)
  have h2 := this.unique P.hasVal_vec
  simpa using h2

section Equivariance
variable [Fintype n] [DecidableEq n]

theorem sum_withLat_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withLat (g • L), F P = ∑ P ∈ withLat L, F (g • P) :=
  (Finset.sum_equiv (MulAction.toPerm g) (fun P => by simp) fun _ _ => rfl).symm

theorem sum_withKer_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withKer (g • L), F P = ∑ P ∈ withKer L, F (g • P) :=
  (Finset.sum_equiv (MulAction.toPerm g) (fun P => by simp) fun _ _ => rfl).symm

def transl : Representation ℂ (GL n k) (Form k n M) where
  toFun g := LinearMap.funLeft ℂ M fun P => g⁻¹ • P
  map_one' := by
    ext φ P
    simp
  map_mul' g h := by
    ext φ P
    simp [mul_smul]

@[simp] theorem transl_apply (g : GL n k) (P : Pair k n) : transl g φ P = φ (g⁻¹ • P) := rfl

variable (π : Representation ℂ (GL n k) M)

def EqForm : Submodule ℂ (Form k n M) where
  carrier := {φ | ∀ (g : GL n k) P, φ (g • P) = π g (φ P)}
  add_mem' h h' g P := by simp [h g P, h' g P]
  zero_mem' g P := by simp
  smul_mem' c φ h g P := by simp [h g P]

def levelVec (P₀ : Pair k n) : Submodule ℂ M where
  carrier := {v | ∀ g : GL n k, g • P₀ = P₀ → π g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]

def formOf (P₀ : Pair k n) (v : levelVec π P₀) : Form k n M := fun P =>
  π (MulAction.exists_smul_eq (GL n k) P₀ P).choose v

theorem formOf_smul (P₀ : Pair k n) (v : levelVec π P₀) (g : GL n k) : formOf π P₀ v (g • P₀) = π g v := by
  have h := (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose_spec
  rw [formOf]
  generalize (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose = g' at h
  have := v.2 (g⁻¹ * g') (by rw [mul_smul, h, inv_smul_smul])
  rw [← mul_inv_cancel_left g g', map_mul, Module.End.mul_apply, this]

theorem formOf_mem (P₀ : Pair k n) (v : levelVec π P₀) : formOf π P₀ v ∈ EqForm π := fun g P => by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
  rw [smul_smul, formOf_smul, formOf_smul, map_mul, Module.End.mul_apply]

def evalEquiv (P₀ : Pair k n) : EqForm π ≃ₗ[ℂ] levelVec π P₀ where
  toFun φ := ⟨φ.1 P₀, fun g hg => by rw [← φ.2 g P₀, hg]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨formOf π P₀ v, formOf_mem π P₀ v⟩
  left_inv φ := Subtype.ext (funext fun P => by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
    exact (formOf_smul π P₀ _ h).trans (φ.2 h P₀).symm)
  right_inv v := Subtype.ext (by simpa using formOf_smul π P₀ v 1)

theorem map_mem_EqForm {T : Module.End ℂ (Form k n M)}
    (h1 : ∀ (g : GL n k) φ P, T φ (g • P) = T (fun Q => φ (g • Q)) P)
    (h2 : ∀ (g : GL n k) (φ : Form k n M) P, T (fun Q => π g (φ Q)) P = π g (T φ P))
    {φ : Form k n M} (h : φ ∈ EqForm π) : T φ ∈ EqForm π := fun g P => by
  rw [h1, ← h2]
  exact congrArg (T · P) (funext (h g))

variable (g : GL n k) (P : Pair k n)

theorem dia_smul (c : 𝓀[k]ˣ) : dia c φ (g • P) = dia c (fun Q => φ (g • Q)) P := by
  simp only [dia_apply, smul_comm g c]

theorem U_smul : U q φ (g • P) = U q (fun Q => φ (g • Q)) P := by
  classical
  simp only [U_apply, Finset.sum_filter, Pair.smul_lat, sum_withKer_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withKer.1 hQ).symm]

theorem FF_smul : FF q χ φ (g • P) = FF q χ (fun Q => φ (g • Q)) P := by
  simp only [FF_apply, Pair.smul_ker, sum_withLat_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withLat.1 hQ)]

theorem FFStar_smul : FFStar q χ φ (g • P) = FFStar q χ (fun Q => φ (g • Q)) P := by
  simp only [FFStar_apply, Pair.smul_lat, sum_withKer_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withKer.1 hQ).symm]

variable {π φ}

theorem dia_mem_EqForm (c : 𝓀[k]ˣ) (h : φ ∈ EqForm π) : dia c φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => dia_smul φ g P c) (fun _ _ _ => rfl) h

theorem U_mem_EqForm (h : φ ∈ EqForm π) : U q φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => U_smul q φ g P) (fun _ _ _ => by simp [U_apply]) h

theorem FF_mem_EqForm (h : φ ∈ EqForm π) : FF q χ φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => FF_smul q χ φ g P) (fun _ _ _ => by simp [FF_apply]) h

theorem FFStar_mem_EqForm (h : φ ∈ EqForm π) : FFStar q χ φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => FFStar_smul q χ φ g P) (fun _ _ _ => by simp [FFStar_apply]) h

end Equivariance
end Forms

section Character
open SplitWeil

theorem apply_int_eq_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (x : 𝒪[k]) : ψ x = 1 :=
  (hψ x).2 (by simpa using (Valuation.mem_integer_iff _ _).1 x.2) x le_rfl

theorem apply_inv_mul_congr {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) {s t : 𝒪[k]}
    (h : residue 𝒪[k] s = residue 𝒪[k] t) : ψ (q.inv * s) = ψ (q.inv * t) := by
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, h, sub_self]))
  have : q.inv * s = q.inv * t + u := by
    have hu' : (s : k) = t + q.1 * u := by exact_mod_cast congrArg Subtype.val (sub_eq_iff_eq_add'.1 hu)
    rw [hu', mul_add, Unif.inv, inv_mul_cancel_left₀ q.ne_zero]
  rw [this, AddChar.map_add_eq_mul, apply_int_eq_one hψ, mul_one]

def resChar (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (q : Unif k) : AddChar 𝓀[k] ℂ where
  toFun a := ψ (q.inv * ((residue_surjective (R := 𝒪[k]) a).choose : 𝒪[k]))
  map_zero_eq_one' := by
    rw [apply_inv_mul_congr hψ q (t := 0) (by rw [(residue_surjective (R := 𝒪[k]) 0).choose_spec, map_zero])]
    simp
  map_add_eq_mul' a b := by
    rw [apply_inv_mul_congr hψ q
      (t := (residue_surjective (R := 𝒪[k]) a).choose + (residue_surjective (R := 𝒪[k]) b).choose)
      (by rw [map_add, (residue_surjective (R := 𝒪[k]) _).choose_spec, (residue_surjective (R := 𝒪[k]) _).choose_spec,
        (residue_surjective (R := 𝒪[k]) _).choose_spec])]
    simp [mul_add, AddChar.map_add_eq_mul]

theorem resChar_residue {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (s : 𝒪[k]) :
    resChar ψ hψ q (residue 𝒪[k] s) = ψ (q.inv * s) :=
  congrArg (fun z : Circle => (z : ℂ)) (apply_inv_mul_congr hψ q (residue_surjective (R := 𝒪[k]) _).choose_spec)

theorem conj_resChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (a : 𝓀[k]) :
    (starRingEnd ℂ) (resChar ψ hψ q a) = resChar ψ hψ q (-a) := by
  obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
  rw [← map_neg, resChar_residue, resChar_residue, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  simp

theorem resChar_ne_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) : resChar ψ hψ q ≠ 1 := by
  intro h
  have h0 : valuation k (q.1 : k) ≠ 0 := (Valuation.ne_zero_iff _).2 q.ne_zero
  have h1 : valuation k q.inv ≤ valuation k ((1 : kˣ) : k) := (hψ q.inv).1 fun y hy => by
    have hy' : (q.1 : k) * y ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      rw [Unif.inv, map_inv₀] at hy
      exact (mul_le_mul_right hy _).trans_eq (mul_inv_cancel₀ h0)
    have := resChar_residue hψ q ⟨_, hy'⟩
    rw [h, AddChar.one_apply, Unif.inv, inv_mul_cancel_left₀ q.ne_zero] at this
    exact Circle.ext this.symm
  have h2 : q.inv ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simpa using h1)
  exact q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero)))

theorem hasConductor_mulShift {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (u : 𝒪[k]ˣ) :
    HasConductor (ψ.mulShift ((u : 𝒪[k]) : k)) 1 := fun x => by
  have hv : ∀ w : 𝒪[k]ˣ, ∀ y : k, valuation k (((w : 𝒪[k]) : k) * y) ≤ valuation k y := fun w y => by
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (w : 𝒪[k]).2)
  rw [← hψ x]
  refine ⟨fun h y hy => ?_, fun h y hy => h _ ((hv u y).trans hy)⟩
  have := h _ ((hv u⁻¹ y).trans hy)
  rwa [AddChar.mulShift_apply, ← mul_assoc, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, one_mul] at this

end Character

section Kernel
variable [Fintype n']

open Classical in

def latInd (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) (x : Matrix n n' k) : ℂ :=
  if ∀ y ∈ S, x *ᵥ y ∈ L then 1 else 0

def Maps (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : Prop :=
  ∃ h : ∀ y ∈ P.lat, x *ᵥ y ∈ Q.lat, ∀ y : P.lat, Q.fn ⟨x *ᵥ y, h y y.2⟩ = P.fn y

open Classical in

def phiOne (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : ℂ := if Maps P Q x then 1 else 0

variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}

theorem maps_iff_hasVal : Maps P Q x ↔ ∀ y a, P.HasVal y a → Q.HasVal (x *ᵥ y) a :=
  ⟨fun ⟨h, h'⟩ y _ ⟨hy, ha⟩ => ⟨h y hy, ha ▸ h' ⟨y, hy⟩⟩,
    fun h => ⟨fun y hy => (h y _ (P.hasVal_fn ⟨y, hy⟩)).mem, fun y => (h y _ (P.hasVal_fn y)).2⟩⟩

theorem maps_iff_glue {e : n' → k} {e' : n → k} (he : P.HasVal e 1) (he' : Q.HasVal e' 1) :
    Maps P Q x ↔ (∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker) ∧ x *ᵥ e - e' ∈ Q.ker := by
  rw [maps_iff_hasVal, ← Pair.hasVal_one_iff he']
  refine ⟨fun h => ⟨fun y hy => Pair.mem_ker.2 (h _ _ (Pair.mem_ker.1 hy)), h _ _ he⟩, fun h y a hy => ?_⟩
  obtain ⟨s, rfl, hs⟩ := (Pair.hasVal_iff he).1 hy
  refine (Pair.hasVal_iff h.2).2 ⟨s, rfl, ?_⟩
  simpa only [mulVec_sub, mulVec_smul] using h.1 _ hs

theorem maps_dia (c : 𝓀[k]ˣ) : Maps (c • P) (c • Q) x ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal]
  exact ⟨fun h y a => by simpa using h y (c * a), fun h y a => h y _⟩

theorem phiOne_dia (c : 𝓀[k]ˣ) : phiOne (c • P) (c • Q) = phiOne P Q := by
  ext x
  classical
  exact if_congr (maps_dia c) rfl rfl

variable [DecidableEq n'] [Fintype n] [DecidableEq n]

theorem maps_smul (g : GL n' k) (h : GL n k) : Maps (g • P) (h • Q) x ↔ Maps P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  simp only [maps_iff_hasVal, Pair.smul_hasVal, ← mulVec_mulVec]
  refine ⟨fun H y a hy => H (g • y) a (by simpa using hy), fun H y a hy => ?_⟩
  have := H _ a hy
  rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this

theorem phiOne_smul (g : GL n' k) (h : GL n k) :
    phiOne (g • P) (h • Q) x = phiOne P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  classical
  exact if_congr (maps_smul g h) rfl rfl

theorem latInd_smul (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) :
    latInd (g • S) (h • L) x = latInd S L ((h⁻¹ : GL n k).val * x * g.val) := by
  have : (∀ y ∈ g • S, x *ᵥ y ∈ h • L) ↔ ∀ y ∈ S, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y ∈ L := by
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  classical
  exact if_congr this rfl rfl

end Kernel

section Glued
variable {c : ℕ}

variable (k n) in

def inX (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (i | i) <;> simp
  map_smul' s x := by ext (i | i) <;> simp

variable (k n) in

def avec (c p : ℕ) : n ⊕ Fin c → k := Sum.elim 0 fun i => if i.val + 1 = p then 1 else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem sum_smul_avec (z : Fin c → k) : ∑ i : Fin c, z i • avec k n c (i.val + 1) = Sum.elim (0 : n → k) z := by
  ext (j | j) <;> simp [avec, Fin.val_inj]

def gluedLat (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c p + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i < p ∧ i ≤ c ∧ y = avec k n c i} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}

def gluedS (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c 1 + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 2 ≤ i ∧ i ≤ c ∧ y = q.inv • avec k n c i}

theorem gluedLat_one (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    gluedLat q c 1 L f = gluedS q c L f := by
  have : {y | ∃ i, 1 ≤ i ∧ i < 1 ∧ i ≤ c ∧ y = avec k n c i} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, h1, h2, -⟩
    omega
  rw [gluedLat, this, Submodule.span_empty, sup_bot_eq]
  rfl

theorem mem_gluedLat {q : Unif k} {p : ℕ} {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} :
    y ∈ gluedLat q c p L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
        (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  let T : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
    { carrier := {y | ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
        (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
          (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k])}
      zero_mem' := ⟨0, by simp, fun i => by simp⟩
      add_mem' := by
        rintro y z ⟨s, hs, h⟩ ⟨t, ht, h'⟩
        refine ⟨s + t, ?_, fun i => ⟨fun hi => add_mem ((h i).1 hi) ((h' i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert add_mem hs ht using 1
          rw [Pi.add_comp, add_smul]
          abel
        · simp [(h i).2.1 hi, (h' i).2.1 hi, mul_add]
        · simpa [mul_add] using add_mem ((h i).2.2 hi) ((h' i).2.2 hi)
      smul_mem' := by
        rintro t y ⟨s, hs, h⟩
        refine ⟨t * s, ?_, fun i => ⟨fun hi => mul_mem t.2 ((h i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert L.smul_mem t hs using 1
          rw [smul_sub, mul_smul]
          rfl
        · change (t : k) * y _ = _
          simp [(h i).2.1 hi, mul_left_comm]
        · change (q.1 : k) * ((t : k) * y _) ∈ _
          rw [mul_left_comm]
          exact mul_mem t.2 ((h i).2.2 hi) }
  have hq : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  constructor
  · refine fun hy => (?_ : gluedLat q c p L f ≤ T) hy
    refine sup_le (sup_le (sup_le ?_ (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩
    · rintro _ rfl
      refine ⟨1, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [inX, avec]
      · simp [inX, avec, hi.ne]
      · simp [inX, avec, hi]
      · simp [inX, avec, hi.ne']
    · rintro _ ⟨j, -, hj, -, rfl⟩
      refine ⟨0, by simp [avec], fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · simp only [avec, Sum.elim_inr]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
    · rintro _ ⟨j, hj, -, rfl⟩
      refine ⟨0, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [avec]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · by_cases h : i.val + 1 = j <;> simp [avec, h, hq]
  · rintro ⟨s, hs, h⟩
    have hy : y = inX k n c (y ∘ Sum.inl - s • f) + s • (q.inv • avec k n c p + inX k n c f) +
        ∑ i : Fin c, (if i.val + 1 = p then 0 else y (Sum.inr i)) • avec k n c (i.val + 1) := by
      rw [sum_smul_avec]
      ext (j | j)
      · simp [inX, avec]
      · have hs' : ∀ z : k, s • z = (s : k) * z := fun _ => rfl
        by_cases hj : j.val + 1 = p
        · simp [inX, avec, Fin.val_inj, hj, (h j).2.1 hj, hs', mul_comm]
        · simp [inX, avec, Fin.val_inj, hj]
    rw [hy]
    refine add_mem (add_mem ?_ ?_) (sum_mem fun i _ => ?_)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, hs, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
    · rcases lt_trichotomy (i.val + 1) p with hi | hi | hi
      · rw [if_neg hi.ne]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ (⟨_, (h i).1 hi⟩ : 𝒪[k])
          (Submodule.subset_span ⟨_, by omega, hi, i.2, rfl⟩)))
      · simp [hi]
      · rw [if_neg hi.ne']
        have := Submodule.smul_mem _ (⟨_, (h i).2.2 hi⟩ : 𝒪[k]) (Submodule.subset_span (R := 𝒪[k])
          (s := {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}) ⟨_, hi, i.2, rfl⟩)
        refine Submodule.mem_sup_right ?_
        convert this using 1
        change _ = ((q.1 : k) * y (Sum.inr i)) • q.inv • avec k n c (i.val + 1)
        rw [smul_smul, mul_right_comm, hq, one_mul]

theorem gluedLat_congr (q : Unif k) (c p : ℕ) {L : Submodule 𝒪[k] (n → k)} {f f' : n → k} (h : f - f' ∈ L) :
    gluedLat q c p L f = gluedLat q c p L f' := by
  ext y
  simp only [mem_gluedLat]
  refine exists_congr fun s => and_congr_left' ?_
  rw [← L.add_mem_iff_left (L.smul_mem s h), smul_sub, sub_add_sub_cancel]

theorem inX_mem_gluedLat {q : Unif k} {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) {L : Submodule 𝒪[k] (n → k)} {f x : n → k} :
    inX k n c x ∈ gluedLat q c p L f ↔ x ∈ L := by
  rw [mem_gluedLat]
  constructor
  · rintro ⟨s, hs, h⟩
    have h0 := (h ⟨p - 1, by omega⟩).2.1 (by simp; omega)
    have : s = 0 := by simpa [inX, Unif.inv, q.ne_zero] using h0
    simpa [this, inX] using hs
  · exact fun hx => ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩

instance gluedLat_isLattice (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k] (f : n → k) :
    (gluedLat q c p L f).IsLattice k := by
  refine ⟨(((hL.fg.map _).sup (Submodule.fg_span_singleton _)).sup (Submodule.fg_span ?_)).sup
    (Submodule.fg_span ?_), ?_⟩
  · exact ((Set.finite_le_nat c).image (avec k n c)).subset fun _ ⟨i, _, _, h, e⟩ => ⟨i, h, e.symm⟩
  · exact ((Set.finite_le_nat c).image (q.inv • avec k n c ·)).subset fun _ ⟨i, _, h, e⟩ => ⟨i, h, e.symm⟩
  · set W := Submodule.span k (gluedLat q c p L f : Set (n ⊕ Fin c → k))
    have hX : ∀ x, inX k n c x ∈ W := fun x => by
      have hx : x ∈ Submodule.span k (L : Set (n → k)) := hL.span_eq_top ▸ trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Submodule.subset_span (mem_gluedLat.2 ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx =>
        convert W.smul_mem a hx using 1
        ext (i | i) <;> simp [inX]
    have hA : ∀ i : Fin c, avec k n c (i.val + 1) ∈ W := fun i => by
      by_cases hi : i.val + 1 = p
      · have h1 : q.inv • avec k n c p + inX k n c f ∈ W := Submodule.subset_span (Submodule.mem_sup_left
          (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
        have h2 := W.smul_mem (q.1 : k) ((W.add_mem_iff_left (hX f)).1 h1)
        rwa [smul_smul, Unif.inv, mul_inv_cancel₀ q.ne_zero, one_smul, ← hi] at h2
      · refine Submodule.subset_span (mem_gluedLat.2 ⟨0, by simp [avec], fun j => ⟨fun _ => ?_, fun hj => ?_, fun _ => ?_⟩⟩)
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
        · simp [avec, show j.val ≠ i.val by omega]
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
    refine eq_top_iff.2 fun y _ => ?_
    have hy : y = inX k n c (y ∘ Sum.inl) + ∑ i : Fin c, y (Sum.inr i) • avec k n c (i.val + 1) := by
      ext (j | j) <;> simp [inX, avec, Fin.val_inj]
    rw [hy]
    exact add_mem (hX _) (sum_mem fun i _ => W.smul_mem _ (hA i))

instance gluedS_isLattice (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : n → k) :
    (gluedS q c L f).IsLattice k := gluedLat_one q c L f ▸ inferInstance

def Pair.glued (P : Pair k n) (q : Unif k) (c p : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) := gluedLat q c p P.ker P.vec

instance (P : Pair k n) (q : Unif k) (c p : ℕ) : (P.glued q c p).IsLattice k := gluedLat_isLattice _ _ _ _ _

variable [Fintype n] [DecidableEq n]

theorem embX_smul_gluedLat (g : GL n k) (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.embX c g • gluedLat q c p L f = gluedLat q c p (g • L) (g • f) := by
  ext y
  have h : (RootEx.embX c g)⁻¹ • y = Sum.elim (g⁻¹ • (y ∘ Sum.inl)) (y ∘ Sum.inr) := by
    rw [← map_inv]
    change fromBlocks (g⁻¹ : GL n k).val 0 0 1 *ᵥ y = _
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, add_zero, zero_add]
    rfl
  simp only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_sub,
    smul_comm g⁻¹, inv_smul_smul]

end Glued

section Spherical
variable [Fintype n] [DecidableEq n]

theorem exists_smul_lat (L L' : Submodule 𝒪[k] (n → k)) [L.IsLattice k] [L'.IsLattice k] :
    ∃ g : GL n k, g • L = L' := by
  let e : L ≃ₗ[𝒪[k]] L' := LinearEquiv.ofFinrankEq _ _ (by
    rw [Submodule.IsLattice.finrank_of_pi k, Submodule.IsLattice.finrank_of_pi k])
  obtain ⟨g, hg⟩ := exists_gl_of_equiv e
  refine ⟨g, Submodule.ext fun x => mem_smul_iff.trans ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← smul_inv_smul g x, hg ⟨_, h⟩]
    exact (e _).2
  · obtain ⟨y, hy⟩ := e.surjective ⟨x, h⟩
    have hx : x = g • (y : n → k) := by rw [hg, hy]
    rw [hx, inv_smul_smul]
    exact y.2

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL n k) A)

def sphVecs (L₀ : Submodule 𝒪[k] (n → k)) : Submodule ℂ A where
  carrier := {v | ∀ g ∈ latStab L₀, σ g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]

def vecAt {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀) (L : Submodule 𝒪[k] (n → k))
    [L.IsLattice k] : A := σ (exists_smul_lat L₀ L).choose v

variable {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀)

end Spherical

section Examples

example [Fintype n] [DecidableEq n] (P : Pair k n) : phiOne P P 1 = 1 :=
  if_pos (maps_iff_hasVal.2 fun y a h => by simpa using h)

example [Fintype n'] (P : Pair k n') (Q : Pair k n) : phiOne P Q 0 = 0 :=
  if_neg fun h => by
    have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec
    rw [zero_mulVec] at h1
    exact one_ne_zero (h1.unique (Pair.mem_ker.1 (zero_mem _)))

example [Fintype n] (i : n) (x : n → k) :
    x ∈ (stdPair k i).ker ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], (⟨x i, h i⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
  simp only [Pair.mem_ker, stdPair_hasVal, residue_eq_zero_iff]

theorem scalar_smul_eq [Fintype n] [DecidableEq n] (g : GL n k) (s : 𝒪[k]ˣ) (hg : ∀ x : n → k, g • x = (s : 𝒪[k]) • x)
    (P : Pair k n) : g • P = (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ • P := by
  refine Pair.ext fun x a => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = g • y := ⟨g⁻¹ • x, (smul_inv_smul g x).symm⟩
  rw [Pair.smul_hasVal, inv_smul_smul, Pair.dia_hasVal, inv_inv, hg]
  refine ⟨fun h => h.smul _, fun h => ?_⟩
  have := h.smul (s⁻¹ : 𝒪[k]ˣ)
  rw [smul_smul, Units.inv_mul, one_smul] at this
  convert this using 1
  change a = _ * (residue 𝒪[k] s * a)
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem Mram_ne_bot [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) : Mram k n ℂ ≠ ⊥ := by
  classical
  obtain ⟨P⟩ : Nonempty (Pair k n) := inferInstance
  intro h
  have h1 := dia_sub_mem_Mram (k := k) (n := n) (Pi.single P (1 : ℂ)) c
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun h1 P
  simp [dia_smul_eq_iff, hc] at h2

example (P : Pair k n) (q : Unif k) (x : n → k) : inX k n 0 x ∈ P.glued q 0 1 ↔ x ∈ P.lat := by
  rw [Pair.glued, mem_gluedLat, Pair.mem_lat_iff]
  simp [inX, Pair.hasVal_iff P.hasVal_vec]

example (r : ℕ) : Nonempty (GluePair k (Fin (r + 1))) := ⟨(stdPair k 0).toGlue⟩

end Examples

end GlobalTheory.LatPair
