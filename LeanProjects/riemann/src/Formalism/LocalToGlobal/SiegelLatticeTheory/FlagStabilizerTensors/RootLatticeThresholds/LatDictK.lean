import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KeyLemmaStatement

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatDictK

section DictK

variable {D : D7} (X : HidaSetting D)

def vOf (x : Fin X.B.I.n → X.B.I.E) : (VS D).V := ∑ i, X.ιE (x i) • X.bas i

theorem crd_vOf (x : Fin X.B.I.n → X.B.I.E) : X.crd (vOf X x) = x := by
  funext i
  simp only [HidaSetting.crd, crdOf, vOf]
  rw [X.bas.repr_sum_self]
  simp

theorem fmatK_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  show X.B.I.fmat (x⁻¹ * x) = 1
  simp [AutInst.fmat]

theorem fmatK_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := rfl

theorem dict_K (a b : X.B.I.Gf) (S : Set (VS D).V)
    (ha : ∀ y, y ∈ S ↔ X.B.I.fmat a⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    (hb : ∀ y, y ∈ S ↔ X.B.I.fmat b⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) : a⁻¹ * b ∈ X.B.I.Kset := by
  have hL : PIW.AdelClassFin.abelian₂ X.B.I a = PIW.AdelClassFin.abelian₂ X.B.I b := by
    ext v
    show X.B.I.fmat a⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf ↔
      X.B.I.fmat b⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf
    have e : PIW.AdelClassFin.iv X.B.I v = incl X.B.I (X.crd (vOf X v)) := by rw [crd_vOf]; rfl
    rw [e]
    exact (ha _).symm.trans (hb _)
  obtain ⟨k, hk, hkeq⟩ := PIW.AdelClassFin.lattice_map_injective X.B.I a b hL
  rw [hkeq, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hk

end DictK

end LatDictK

open LatDictK

section DictKMain

variable {D : D7} (X : HidaSetting D)

theorem colLatK {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) :
    Formalism.L2.SG.NormCut.ColLatK cs := by
  intro ρ σ h
  refine dict_K X _ _ {y | y ∈ cs.lamOf ρ} (fun y => cs.lat_eq ρ y) (fun y => ?_)
  show y ∈ cs.lamOf ρ ↔ _
  rw [h]
  exact cs.lat_eq σ y

end DictKMain

namespace LatDictK

section DictK2

variable {D : D7} (X : HidaSetting D)

theorem ratLink_incl {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (w : (VS D).V) :
    X.B.I.fmat x.2 *ᵥ incl X.B.I (X.crd w) = incl X.B.I (X.crd (γ w)) := by
  obtain ⟨M, -, -, hf, hc⟩ := h
  have h3 : incl X.B.I ((M : Matrix _ _ _) *ᵥ X.crd w) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd w) := by
    funext i
    exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (M : Matrix _ _ _) (X.crd w) i
  rw [hf, hc, h3]

theorem ratLink_incl_inv {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (y : (VS D).V) :
    X.B.I.fmat x.2⁻¹ *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (γ.symm y)) := by
  conv_lhs => rw [← γ.apply_symm_apply y, ← ratLink_incl X h]
  rw [mulVec_mulVec, fmatK_inv_mul, one_mulVec]

end DictK2

end LatDictK

section DictKMain2

variable {D : D7} (X : HidaSetting D)

theorem termK {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows') :
    Formalism.L2.SG.NormCut.TermK F0 F0' cs cs' := by
  intro t
  obtain ⟨hRL, -, hmap, -⟩ := t.rep.2
  have hRL' : RatLink X t.pt t.lin := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := hmap
  have hb0 := cs.base_lam t.lam t.mem
  have hb1 := cs'.base_lam t.lam' t.mem'
  have key : ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
      (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine dict_K X _ _ {y | y ∈ t.lam} (fun y => ?_) (fun y => ?_)
    · show y ∈ t.lam ↔ _
      conv_lhs => rw [← hb0]
      exact cs.lat_eq _ y
    · show y ∈ t.lam ↔ _
      have e1 : y ∈ t.lam ↔ t.lin.symm y ∈ t.lam' := by
        rw [← hmap']
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : t.lin.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          exact ⟨t.lin.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ t.lam' ↔ X.B.I.fmat ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := cs'.lat_eq (cs'.base t.lam') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u'))⁻¹ =
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * t.pt.2⁻¹ from _root_.mul_inv_rev _ _,
        fmatK_mul, ← mulVec_mulVec, ratLink_incl_inv X hRL']
  have e : kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt =
      ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf, mul_assoc]
  rw [e]
  exact key

end DictKMain2

namespace LatDictK

section DictK3

variable {D : D7} (X : HidaSetting D)

theorem nat_split (g : ℕ) : ∀ m : ℕ, 0 < m → ∃ c d : ℕ, m = c * d ∧ Nat.Coprime c g ∧ d ∣ g ^ m :=
  _root_.UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main g

theorem mem_of_loc {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (L : Submodule R M) (x : M)
    (h : ∀ Q : Ideal R, Q.IsMaximal → ∃ s, s ∉ Q ∧ s • x ∈ L) : x ∈ L := by
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R M x)
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  · obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsx⟩ := h Q hQ
    exact absurd (hIQ (show s ∈ I by simpa [I] using hsx)) hs

theorem crd_nsmul (n : ℕ) (v : (VS D).V) : X.crd (n • v) = n • X.crd v := by
  funext i
  simp [HidaSetting.crd, crdOf, map_nsmul]

theorem incl_nsmul (n : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (n • x) = (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I x := by
  funext i
  simp [incl, nsmul_eq_mul]

end DictK3

end LatDictK

section DictKMain3

variable {D : D7} (X : HidaSetting D)

theorem modGAt : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hg : X.B.g = gS D := X.g_eq
  obtain ⟨m, hm0, hm⟩ := PIW.AdelClassFin.lattice_denominator X.B.I (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v))
  have hmv : m • v ∈ Λ := by
    rw [hΛ, crd_nsmul, incl_nsmul, mulVec_smul]
    exact hm
  obtain ⟨c, d, hmcd, hcop, hdg⟩ := nat_split X.B.g m hm0
  have hcv : c • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    apply mem_of_loc
    intro Q hQ
    by_cases hgQ : ((gS D : ℕ) : 𝓞 D.host.E) ∈ Q
    · have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField _)
      obtain ⟨s, hs, hsv⟩ := hv ⟨Q, hQ.isPrime, hQ0⟩ hgQ
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_of_tower_mem _ c hsv
    · refine ⟨((gS D * d : ℕ) : 𝓞 D.host.E), fun hQd => ?_, ?_⟩
      · rw [Nat.cast_mul] at hQd
        rcases hQ.isPrime.mem_or_mem hQd with h1 | h1
        · exact hgQ h1
        · obtain ⟨k, hk⟩ := hdg
          have h2 : ((X.B.g ^ m : ℕ) : 𝓞 D.host.E) ∈ Q := by
            rw [hk, Nat.cast_mul]; exact Q.mul_mem_right _ h1
          rw [Nat.cast_pow, hg] at h2
          exact hgQ (hQ.isPrime.mem_of_pow_mem _ h2)
      · have e : ((gS D * d : ℕ) : 𝓞 D.host.E) • (c • v) = ((gS D : ℕ) : 𝓞 D.host.E) • (m • v) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_smul, smul_smul, hmcd]
          ring_nf
        rw [e]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hmv
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  refine ⟨c, hcop, ?_⟩
  have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd w)) := by
    rw [← mulVec_smul, ← mulVec_smul, ← incl_nsmul, ← incl_nsmul, ← crd_nsmul, ← crd_nsmul, ← hwv,
      Nat.cast_smul_eq_nsmul, hg]
  rw [e2]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, rfl⟩

end DictKMain3

end Formalism.L2.SG.Pf
