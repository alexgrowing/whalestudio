import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_of_inv {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hm : MuUnit V dict mu)
    (hP : ∀ g, ∀ γ' ∈ (X (dict g).1).Γ, P (dict g).1 (lact γ' (dict g).2) = P (dict g).1 (dict g).2) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  exact congrArg (mu g * ·) (hP g γ' hγ')

theorem adel_leftInv_of_chi {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g :=
  adel_leftInv_of_inv V dict mu P hd hm fun g γ' hγ' => by
    rw [hΓ _ γ' hγ' _ (hdom g), hχ _ γ' hγ', one_mul]

end Models

section Readings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdInvG (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
    rdU U f k (lact γ x) = rdU U f k x

def SecGen (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ k, ∃ b m, Dom b m ∧
    (∃ f ∈ sec Xo c b m, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) ∧
    (∃ f ∈ sec Xo c (a + b) (n + m), ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0)

variable (U : Unf Xo c σ r)

theorem laU_add_even (a b : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (hn : Even n) (hm : Even m) (k : U.Comp) :
    laU U (a + b) (n + m) k = laU U a n k + laU U b m k := by
  have h2 : (n + m) / 2 = n / 2 + m / 2 := by
    obtain ⟨x, rfl⟩ := hn
    obtain ⟨y, rfl⟩ := hm
    omega
  funext τ j
  simp only [laU, Pi.add_apply, h2]
  split_ifs <;> push_cast <;> ring

theorem Dom.add' {a b : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} (ha : Dom a n) (hb : Dom b m) : Dom (a + b) (n + m) :=
  ⟨fun τ _ _ hij => Nat.add_le_add (ha.1 τ hij) (hb.1 τ hij), ha.2.add hb.2⟩

theorem rdU_lact (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (k : U.Comp) :
    ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, rdU U f k (lact γ x) = (U.X k).χ (laU U a n k) γ * rdU U f k x :=
  (hU.2.2.2.2.1 a n hdn f hf k).2.2

theorem chi_eq_one_of_read (hU : IsUnf U) (hR : RdInvG U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {k : U.Comp} {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) (h0 : rdU U f k x ≠ 0) :
    (U.X k).χ (laU U a n k) γ = 1 := by
  have e1 := rdU_lact U hU hdn hf k γ hγ x hx
  rw [hR a n hdn f hf k γ hγ x hx] at e1
  have e2 : ((U.X k).χ (laU U a n k) γ - 1) * rdU U f k x = 0 := by
    rw [sub_mul, ← e1]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right h0)

theorem chiTriv_of (hU : IsUnf U) (hR : RdInvG U) (hS : SecGen U) :
    ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1 := by
  intro a n hdn k γ hγ
  obtain ⟨b, m, hbm, ⟨f1, hf1, x1, hx1, h1⟩, ⟨f2, hf2, x2, hx2, h2⟩⟩ := hS a n hdn k
  have e1 := chi_eq_one_of_read U hU hR hbm hf1 hγ hx1 h1
  have e2 := chi_eq_one_of_read U hU hR (Dom.add' hdn hbm) hf2 hγ hx2 h2
  rw [laU_add_even U a b n m hdn.2 hbm.2 k, (U.X k).χ_add _ _ γ hγ, e1, mul_one] at e2
  exact e2

theorem rdInvG_of_chi (hU : IsUnf U)
    (hχ : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) : RdInvG U := by
  intro a n hdn f hf k γ hγ x hx
  rw [rdU_lact U hU hdn hf k γ hγ x hx, hχ a n hdn k γ hγ, one_mul]

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
  (Kf : Subgroup (GA D V)) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)

theorem rdU_leftInv (hU : IsUnf U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_chi V dict mu (laU U a n) (rdU U f) hd.1 hd.2.2.2.1 hm (rdU_lact U hU hdn hf) hχ

theorem rdU_leftInv_of_rdInvG (hR : RdInvG U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_inv V dict mu (rdU U f) hd.1 hm fun g γ' hγ' => hR a n hdn f hf _ γ' hγ' _ (hd.2.2.2.1 g)

end Readings

namespace Core

variable {D : D7} (T : Core D)

theorem chiTriv_of_clauses (hunf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ))
    (hR : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → RdInvG (T.U j σ))
    (hS : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → SecGen (T.U j σ)) :
    ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
      ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1 :=
  fun j hj σ hσ => chiTriv_of (T.U j σ) (hunf j hj σ hσ) (hR j hj σ hσ) (hS j hj σ hσ)

theorem phiAd_leftInv_of_rdInvG {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hR : RdInvG (T.U j σ))
    (hdU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr)
    (hm : MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : T.R j} (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g := by
  obtain ⟨th, hr, -, hd⟩ := hdU
  intro γ hγ g
  unfold phiAd
  simp only [Pi.smul_apply]
  rw [rdU_leftInv_of_rdInvG (T.U j σ) (T.V j σ) (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hr hR hd hm hdn hf γ hγ g]

end Core

theorem LawsM.phiAd_leftInv {D : D7} {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g :=
  T.phiAd_leftInv_of_rdInvG
    (rdInvG_of_chi (T.U j σ) (h.unf j hj σ hσ) (h.chiTriv j hj σ hσ)) (h.dictU j hj σ hσ)
    (h.muUnit j hj σ hσ) hdn hf

theorem LawsM.phiAd_leftInv_cusp {D : D7} {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j)
    {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : T.R j} (hf : f ∈ T.cuspA j a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g :=
  h.phiAd_leftInv hj hσ hdn (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n hf)

end Formalism.L2.Pj
