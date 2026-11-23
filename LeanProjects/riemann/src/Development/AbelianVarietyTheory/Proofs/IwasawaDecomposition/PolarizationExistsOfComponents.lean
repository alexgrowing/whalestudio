import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletionStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

theorem asm_invFun_ext {O : Type} [CommRing O] {φ ψ : InvFun O} (h : ∀ n B, φ.toFun n B = ψ.toFun n B) : φ = ψ := by
  cases φ; cases ψ; congr; funext n B; exact h n B

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem asm_isTwInv_comb {H : Host E} {ψ φ : InvFun (𝓞 E)} (a b : ℕ) (hψ : IsTwInv H ψ) (hφ : IsTwInv H φ) :
    IsTwInv H (comb a ψ b φ) := fun σ hσ n B => by
  show _ * ψ.toFun n _ + _ * φ.toFun n _ = _ * ψ.toFun n _ + _ * φ.toFun n _
  rw [hψ σ hσ, hφ σ hσ]

theorem asm_isTwInv_resInt (H : Host E) (φs : InvFun ℤ) : IsTwInv H (resInt (𝓞 E) φs) := fun σ _ n B => by
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) := LinearEquiv.piCongrRight fun _ => σ.toAddEquiv.toIntLinearEquiv
  exact φs.eval_equiv e B

theorem asm_isTame_resInt {O : Type} [CommRing O] [Module.Finite ℤ O] {φs : InvFun ℤ} (h : IsTame φs) :
    IsTame (resInt O φs) := ⟨fun n k B => h.1 _ k _, fun n B => h.2 _ _⟩

theorem asm_isTame_comb {O : Type} [CommRing O] {ψ φ : InvFun O} (a b : ℕ) (hψ : IsTame ψ) (hφ : IsTame φ) :
    IsTame (comb a ψ b φ) := by
  refine ⟨fun n k B => ?_, fun n B => ?_⟩
  · show _ * ψ.toFun n _ + _ * φ.toFun n _ = _ * (_ * ψ.toFun n _ + _ * φ.toFun n _)
    rw [hψ.1, hφ.1]; ring
  · show 0 ≤ _ * ψ.toFun n _ + _ * φ.toFun n _
    have := hψ.2 n B; have := hφ.2 n B; positivity

theorem asm_isPosFn_comb {H : Host E} {ψ φ : InvFun (𝓞 E)} (a : ℕ) {b : ℕ} (hb : 0 < b) (hψ : IsTame ψ)
    (hφ : IsPosFn H φ) : IsPosFn H (comb a ψ b φ) := by
  intro X _ _ _ _ be hbe hp
  have h1 : 0 ≤ ψ.evalZ be := hψ.2 _ _
  have h2 := hφ X be hbe hp
  show 0 < _ * ψ.evalZ be + _ * φ.evalZ be
  have : (0:ℝ) < b := by exact_mod_cast hb
  positivity

theorem asm_hasCones_fine {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {Z : GMod Xo c} {φs : InvFun ℤ} {𝒩 : Finset ℕ} {φ : InvFun (𝓞 E)} (hφ : Refines H (min D.p D.q) φs 𝒩 φ)
    (hZ : HasCones (ConeO H φ) Z) : HasCones (fun _ _ _ _ _ γ => ∀ N ∈ 𝒩, IsFine N γ) Z := by
  intro z
  obtain ⟨R, i1, i2, i3, ξ, t, hm, P, m, γ, hCN, hz, het, hfu, hti, hcn, hin⟩ := hZ z
  have hrk := GlobalTheory.T.formally_unramified_etale_completion E H D l Xo c Z R ξ t hm P hCN het hfu hti
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  exact ⟨R, i1, i2, i3, ξ, t, hm, P, m, γ, hCN, hz, het, hfu, hti, (hφ.2.2.2.2.2 _ hrk m γ hcn).2, hin⟩

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem asm_isDedFrac_id (F : Type) [Field F] [CharZero F] : IsDedFrac (RingHom.id F) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.2 fun _ h => (IsUnit.mk0 _ (nonZeroDivisors.ne_zero h))⟩

theorem polExSt_of_steps : PolSuppSt → SiegLocSt → PolGlueSt → PhiDivZSt → PhiDivOSt → UniformSt → RefineSt → GenFanSt →
    GenMapSt → BlowExSt → BlowOrdSt → BlowPolSt → ConeArcSt → DomSt → PolExSt := by
  intro hSu hSg hGl hPZ hPO hUn hRf hGF hGM hBE hBO hBP hCA hDo
  intro E _ _ _ H D h1 Xo
  obtain ⟨s, 𝒩, h𝒩, hdom⟩ := hDo E H D h1 Xo
  obtain ⟨g, φs, hg, hfan, htame, hloc⟩ := hSg E H D h1 Xo
  have hrtw : IsTwInv H (resInt (𝓞 E) φs) := asm_isTwInv_resInt H φs
  have h0tw : IsTwInv H (comb 0 (resInt (𝓞 E) φs) 0 (resInt (𝓞 E) φs)) := asm_isTwInv_comb 0 0 hrtw hrtw
  have hX : ∀ (l : Level H) (c : Coeff l) (hgd : ∀ p : ℕ, p.Prime → l.GoodAt p), ∃ X : GMod (Xo l) c,
      HasCones (ConeZ E φs) X ∧ PolRay (comb 0 (resInt (𝓞 E) φs) 0 (resInt (𝓞 E) φs)) (resInt (𝓞 E) φs) 1 X := by
    intro l c hgd
    obtain ⟨I, hI, R, hR, a, b, ω, C, hcov, hC⟩ := hloc l c hgd
    exact hGl E H D l (Xo l) c I hI R hR a b ω C _ _ 1 _ h0tw hrtw hcov hC
  choose X hXc hXr using hX
  obtain ⟨a, b, ha, hb, hXp⟩ := hUn E H D h1 Xo _ _ 1 X h0tw hrtw
    (fun l c hgd => ⟨hXr l c hgd, fun a b => hPZ E H D l (Xo l) c (X l c hgd) g φs hg hfan (hXc l c hgd) a b⟩)
  obtain ⟨φ', hφ'⟩ := hRf E H (min D.p D.q) g φs 𝒩 hg hfan h𝒩
  obtain ⟨hpf, hns, htw', hpos', htame', -⟩ := id hφ'
  have hψeq : comb a (comb 0 (resInt (𝓞 E) φs) 0 (resInt (𝓞 E) φs)) b (resInt (𝓞 E) φs) =
      comb b (resInt (𝓞 E) φs) 0 φ' := asm_invFun_ext fun n B => by
    show (a : ℝ) * ((0 : ℕ) * _ + (0 : ℕ) * _) + _ = _ + ((0 : ℕ) : ℝ) * _
    simp
  have hψtw : IsTwInv H (comb b (resInt (𝓞 E) φs) 0 φ') := asm_isTwInv_comb b 0 hrtw htw'
  have hψtame : IsTame (comb b (resInt (𝓞 E) φs) 0 φ') := asm_isTame_comb b 0 (asm_isTame_resInt htame) htame'
  have hXP : ∀ l c hgd, ∃ DX, IsPol (comb b (resInt (𝓞 E) φs) 0 φ') a (X l c hgd) DX := fun l c hgd => by
    obtain ⟨DX, h⟩ := hXp l c hgd
    rw [hψeq, mul_one] at h
    exact ⟨DX, h⟩
  have hZ : ∀ (l : Level H) (c : Coeff l) (hgd : ∀ p : ℕ, p.Prime → l.GoodAt p), ∃ Z : GMod (Xo l) c,
      HasCones (ConeO H φ') Z ∧ PolRay (comb b (resInt (𝓞 E) φs) 0 φ') φ' a Z ∧ GenTor Z := by
    intro l c hgd
    obtain ⟨DX, hDX⟩ := hXP l c hgd
    obtain ⟨Y, BY, d, k, hd, hYt, hYc, hYp⟩ := hGF E H D h1 φ' hpf hns l (Xo l) c
    obtain ⟨ρ, hρ⟩ := hGM E H D l (Xo l) c (X l c hgd) Y g φs 𝒩 φ' b a DX hg hfan hφ' hDX hYc
    have hsupp : ∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G := fun x hx =>
      (hSu E H D l (Xo l) c c.F (RingHom.id c.F) Y BY (comb 0 φ' d φ') (asm_isDedFrac_id c.F)
        (asm_isPosFn_comb 0 hd htame' hpos') hYp.1 x).1 hx
    obtain ⟨Z, π, e, J, EX, n, hbl⟩ := hBE E H D l (Xo l) c (X l c hgd) Y BY k ρ hρ hYp.2 hsupp
    have hN4 := hCA E H D h1 Xo l c hgd (X l c hgd) _ a DX hψtame hDX
    obtain ⟨hZd, hZc⟩ := hBO E H D l (Xo l) c (X l c hgd) Z Y BY π e J EX n b d a g φs 𝒩 φ' DX hg hfan hφ'
      (hXc l c hgd) hN4 hDX hd hYp.1 hbl
    obtain ⟨hZr, hZt⟩ := hBP E H D l (Xo l) c (X l c hgd) Z Y BY π e J EX n a (n * d) _ φ' DX hDX hbl
      (Nat.mul_pos hbl.1 hd) hZd hYt
    exact ⟨Z, hZc, hZr, hZt⟩
  choose Z hZc hZr hZt using hZ
  obtain ⟨a', b', ha', hb', hZp⟩ := hUn E H D h1 Xo _ φ' a Z hψtw htw'
    (fun l c hgd => ⟨hZr l c hgd, fun a'' b'' =>
      hPO E H D l (Xo l) c (Z l c hgd) g φs 𝒩 φ' hg hfan hφ' (hZc l c hgd) a'' b b''⟩)
  have htf : IsTame (comb a' (comb b (resInt (𝓞 E) φs) 0 φ') b' φ') := asm_isTame_comb a' b' hψtame htame'
  refine ⟨s, comb a' (comb b (resInt (𝓞 E) φs) 0 φ') b' φ', a' * a, Nat.mul_pos ha' ha,
    asm_isTwInv_comb a' b' hψtw htw', asm_isPosFn_comb a' hb' hψtame hpos', htf.1, fun l c hgd => ?_⟩
  obtain ⟨BD, hBD⟩ := hZp l c hgd
  obtain ⟨hsm, hsnc, htor⟩ := hZt l c hgd
  exact ⟨Z l c hgd, BD, hdom l c hgd _ (asm_hasCones_fine hφ' (hZc l c hgd)), hBD, hsm, hsnc, htor⟩

end GlobalTheory.TorRef
