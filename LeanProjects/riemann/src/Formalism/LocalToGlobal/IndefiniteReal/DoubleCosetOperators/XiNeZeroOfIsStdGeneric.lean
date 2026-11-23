import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

def mulC {q : ℕ} (c : ZMod q) : Multiplicative (ZMod q) →* Multiplicative (ZMod q) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)

@[simp] theorem mulC_ofAdd {q : ℕ} (c z : ZMod q) :
    mulC c (Multiplicative.ofAdd z) = Multiplicative.ofAdd (c * z) := rfl

theorem comp_mulC_ne_one {K : Type} [Field K] {q : ℕ} [Fact q.Prime] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1)
    {c : ZMod q} (hc : c ≠ 0) : θ.comp (mulC c) ≠ 1 := by
  intro h
  apply hθ
  refine MonoidHom.ext fun z => ?_
  have e := DFunLike.congr_fun h (Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd z))
  simp only [MonoidHom.comp_apply, mulC_ofAdd, MonoidHom.one_apply] at e
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, ofAdd_toAdd] at e
  simpa using e

theorem comp_mulC_zero {K : Type} [Field K] {q : ℕ} (θ : Multiplicative (ZMod q) →* Kˣ) :
    θ.comp (mulC (0 : ZMod q)) = 1 := by
  refine MonoidHom.ext fun z => ?_
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
  rw [← ofAdd_toAdd z, mulC_ofAdd, zero_mul, ofAdd_zero, map_one]

section Gen

variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)

def thXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) :
    ∀ x, Multiplicative (ZMod (p x)) →* Kˣ :=
  fun x => (θ x).comp (mulC (ξ x))

def psiXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) : Uup p r →* Kˣ :=
  psiStd p r (thXi p ξ θ)

variable {p r}

theorem psiXi_apply {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (u : Uup p r) : psiXi p r ξ θ u = ∏ x, θ x (Multiplicative.ofAdd (ξ x *
      supSum r (((u : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))))) := rfl

theorem supSum_mul_Uup (u v : Uup p r) (x : ι) :
    supSum r ((((u * v : Uup p r) : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) =
      supSum r (((u : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) +
      supSum r (((v : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) := by
  simpa using supSum_mul (u.2 x) (v.2 x)

theorem psiXi_mul {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (u v : Uup p r) : psiXi p r ξ θ (u * v) = psiXi p r ξ θ u * psiXi p r ξ θ v := map_mul _ u v

theorem psiXi_isStdGeneric {K : Type} [Field K] (hp : ∀ x, (p x).Prime) (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hξ : 2 ≤ r → ∀ x, ξ x ≠ 0) (hθ : 2 ≤ r → ∀ x, θ x ≠ 1) :
    IsStdGeneric p r (psiXi p r ξ θ) := by
  refine ⟨thXi p ξ θ, fun hr x => ?_, fun u => rfl⟩
  haveI := Fact.mk (hp x)
  exact comp_mulC_ne_one (θ x) (hθ hr x) (hξ hr x)

theorem psiXi_tvAt [DecidableEq ι] {K : Type} [Field K] (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hr : 2 ≤ r) (x : ι) :
    psiXi p r ξ θ ⟨tvAt hr x, tvAt_mem hr x⟩ = θ x (Multiplicative.ofAdd (ξ x)) := by
  have hc : ∀ M : Matrix.SpecialLinearGroup (Fin r) (ZMod (p x)),
      ((Matrix.SpecialLinearGroup.toGL M : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) = M :=
    fun M => rfl
  rw [psiXi_apply, Finset.prod_eq_single x]
  · simp only [tvAt, Pi.mulSingle_eq_same]
    show θ x (Multiplicative.ofAdd (ξ x * supSum r (tv hr (1 : ZMod (p x))))) = _
    rw [supSum_tv, mul_one]
  · intro y _ hy
    simp [tvAt, Pi.mulSingle_eq_of_ne hy, supSum_one]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem psiXi_ne_one [DecidableEq ι] {K : Type} [Field K] (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hr : 2 ≤ r) (x : ι) (hp : (p x).Prime) (hξ : ξ x ≠ 0)
    (hθ : θ x ≠ 1) : psiXi p r ξ θ ≠ 1 := by
  intro h
  have h1 := psiXi_tvAt ξ θ hr x
  rw [h, MonoidHom.one_apply] at h1
  apply hθ
  haveI : Fact (p x).Prime := ⟨hp⟩
  haveI : NeZero (p x) := ⟨hp.ne_zero⟩
  refine MonoidHom.ext fun z => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Multiplicative.toAdd z = n • ξ x :=
    ⟨(Multiplicative.toAdd z * (ξ x)⁻¹).val, by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hξ, mul_one]⟩
  rw [MonoidHom.one_apply, ← ofAdd_toAdd z, hn, ofAdd_nsmul, map_pow, ← h1, one_pow]

theorem xi_ne_zero_of_isStdGeneric [DecidableEq ι] {K : Type} [Field K] {S : Subgroup (GProd p r)}
    (hS : S = Uup p r) (ψ : S →* Kˣ) (hg : IsStdGeneric p r ψ) (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hψ : ∀ u : S, ψ u = stdVal p r (thXi p ξ θ) u)
    (hr : 2 ≤ r) (hp : ∀ x, NeZero (p x)) (x : ι) : ξ x ≠ 0 := by
  intro h0
  obtain ⟨θ', hθ', hψ'⟩ := hg
  have hm : tvAt (p := p) hr x ∈ S := by rw [hS]; exact tvAt_mem hr x
  have e := (hψ' ⟨_, hm⟩).symm.trans (hψ ⟨_, hm⟩)
  simp only [stdVal_tvAt, thXi, h0, comp_mulC_zero, MonoidHom.one_apply] at e
  exact char_one_ne (θ' x) (hθ' hr x) e

end Gen

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def U (N : NData R H what₂) : Subgroup (G0g N) :=
  Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r

theorem U_eq_Uup (N : NData R H what₂) : U N = Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r := rfl

theorem mem_U {N : NData R H what₂} {u : G0g N} : u ∈ U N ↔
    ∀ kv : (Σ k : Fin 2, N.PlG k), (∀ a b : Fin R.r, b < a →
      ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a b = 0) ∧
      ∀ a : Fin R.r, ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a a = 1 :=
  Iff.rfl

theorem U_ne_bot (N : NData R H what₂) (hr : 2 ≤ R.r) (k : Fin 2) (v : N.PlG k) : U N ≠ ⊥ := by
  classical
  intro h
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  have hm : tvAt (p := fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) hr ⟨k, v⟩ ∈ U N := tvAt_mem hr _
  rw [h, Subgroup.mem_bot] at hm
  have e := congrArg (fun g : G0g N =>
    supSum R.r ((g ⟨k, v⟩ : GL (Fin R.r) (ZMod (H.g k))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k)))) hm
  simp only [tvAt_apply, if_true] at e
  rw [supSum_tv] at e
  simp [supSum_one] at e

def psiUOf (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) : U N →* Kˣ :=
  psiXi (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r ξ (fun kv => θ kv.1)

theorem psiUOf_apply (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) (u : U N) :
    psiUOf N ξ θ u = ∏ kv : (Σ k : Fin 2, N.PlG k), θ kv.1 (Multiplicative.ofAdd (ξ kv *
      supSum R.r (((u : G0g N) kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))))) :=
  rfl

theorem psiUOf_isStdGeneric (N : NData R H what₂) {K : Type} [Field K]
    (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1)) (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ)
    (hξ : 2 ≤ R.r → ∀ kv, ξ kv ≠ 0) (hθ : 2 ≤ R.r → ∀ k, θ k ≠ 1) :
    IsStdGeneric (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r (psiUOf N ξ θ) :=
  psiXi_isStdGeneric (fun kv : (Σ k : Fin 2, N.PlG k) => H.g_prime kv.1) ξ _ hξ
    (fun hr (kv : Σ k : Fin 2, N.PlG k) => hθ hr kv.1)

theorem psiUOf_ne_one (N : NData R H what₂) {K : Type} [Field K]
    (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1)) (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ)
    (hr : 2 ≤ R.r) (k : Fin 2) (v : N.PlG k) (hξ : ξ ⟨k, v⟩ ≠ 0) (hθ : θ k ≠ 1) : psiUOf N ξ θ ≠ 1 := by
  classical
  exact psiXi_ne_one ξ (fun kv => θ kv.1) hr ⟨k, v⟩ (H.g_prime k) hξ hθ

def thSide {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ) (b : Bool) :
    ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ :=
  fun k => if b then θ k else (θ k)⁻¹

theorem thSide_ne_one {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ)
    (b : Bool) (k : Fin 2) (h : θ k ≠ 1) : thSide g θ b k ≠ 1 := by
  cases b <;> simp [thSide, h]

def psiUD (D : D7) (i : D.ntw.Tw) (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (b : Bool) : U D.nd →* (FractionRing (D.ntw.O i))ˣ :=
  psiUOf D.nd (xiRed D) (thSide D.host.g θ b)

theorem psiUD_side (D : D7) (i : D.ntw.Tw)
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ) (u : U D.nd) :
    psiUD D i θ false u = (psiUD D i θ true u)⁻¹ := by
  simp only [psiUD, psiUOf_apply, thSide, Bool.false_eq_true, if_false, if_true, MonoidHom.inv_apply,
    Finset.prod_inv_distrib]

def XiRedNZ (D : D7) : Prop := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), xiRed D kv ≠ 0

theorem tied_U_clauses (D : D7)
    (θ : ∀ i, ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (hξ : 2 ≤ D.R.r → XiRedNZ D) (hθ : 2 ≤ D.R.r → ∀ i k, θ i k ≠ 1)
    (hU : D.nexp.U = U D.nd)
    (hψ : ∀ i b (u : D.nexp.U), D.nexp.psiU i b u = psiUD D i (θ i) b ⟨u.1, by rw [← hU]; exact u.2⟩) :
    D.nexp.U = Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ∧
    (∀ i b, IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r (D.nexp.psiU i b)) ∧
    (∀ i (u : D.nexp.U), D.nexp.psiU i false u = (D.nexp.psiU i true u)⁻¹) ∧
    (∀ i b, ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ,
      (2 ≤ D.R.r → ∀ kk, θ kk ≠ 1) ∧ ∀ u : D.nexp.U, D.nexp.psiU i b u = ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
        θ kv.1 (Multiplicative.ofAdd (xiRed D kv *
          supSum D.R.r (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))) := by
  refine ⟨hU, fun i b => ?_, fun i u => ?_, fun i b => ?_⟩
  · refine ⟨thXi _ (xiRed D) (fun kv => thSide D.host.g (θ i) b kv.1), fun hr kv => ?_, fun u => ?_⟩
    · have : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
      exact comp_mulC_ne_one _ (thSide_ne_one _ _ b _ (hθ hr i kv.1)) (hξ hr kv)
    · rw [hψ]; rfl
  · rw [hψ, hψ]; exact psiUD_side D i (θ i) _
  · exact ⟨thSide D.host.g (θ i) b, fun hr kk => thSide_ne_one _ _ b _ (hθ hr i kk), fun u => by rw [hψ]; rfl⟩

theorem NExpTied.xiRedNZ {D : D7} (T : NExpTied D) (hr : 2 ≤ D.R.r) (i : D.ntw.Tw) : XiRedNZ D := by
  classical
  intro kv
  obtain ⟨θ, -, hψ⟩ := T.psiU_xi i true
  exact xi_ne_zero_of_isStdGeneric T.U_eq _ (T.psiU_gen i true) (xiRed D) (fun kv => θ kv.1)
    (fun u => (hψ u).trans rfl) hr (fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩) kv

end Rec

section PerPlace

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def psiUPl (N : NData R H what₂) {K : Type} [Field K]
    (ψ : ∀ kv : (Σ k : Fin 2, N.PlG k), Multiplicative (ZMod (H.g kv.1)) →* Kˣ) : U N →* Kˣ :=
  psiStd (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r ψ

theorem psiUOf_eq_psiUPl (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) :
    psiUOf N ξ θ = psiUPl N (thXi (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) ξ (fun kv => θ kv.1)) := rfl

def psiUPlSide (N : NData R H what₂) {K : Type} [Field K]
    (ψ : ∀ kv : (Σ k : Fin 2, N.PlG k), Multiplicative (ZMod (H.g kv.1)) →* Kˣ) (b : Bool) : U N →* Kˣ :=
  if b then psiUPl N ψ else (psiUPl N ψ)⁻¹

end PerPlace

end Formalism.IndefR.NX
