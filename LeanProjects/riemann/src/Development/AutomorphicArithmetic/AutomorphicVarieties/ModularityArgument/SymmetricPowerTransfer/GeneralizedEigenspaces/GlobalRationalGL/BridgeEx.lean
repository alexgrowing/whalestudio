import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.QuaternionDoubleCosetIndicator

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

open Loc Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

abbrev un (w : Plc L) : Pl (Lp L) := w.under (𝓞 (Lp L))

abbrev cjF : Af L →+* Af L := conjFin (IsCMField.complexConj L).toRingEquiv

variable (L) in

structure RingBr where
  Δ : Lp L
  e : Lsq (Lp L) Δ ≃+* L
  e_star : ∀ x, e (star x) = IsCMField.complexConj L (e x)
  e_alg : ∀ a : Lp L, e (algebraMap _ _ a) = algebraMap (Lp L) L a
  neg : ∀ σ : Lp L →+* ℝ, σ Δ < 0
  loc : ∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal → IsLoc (Ov v) (cv v Δ)
  ρ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Lsq (Kv v) (cv v Δ) →+* Kw w
  ρ_glob : ∀ v w h (x : Lsq (Lp L) Δ), ρ v w h (lmap (cv v) Δ x) = algebraMap L (Kw w) (e x)
  ρ_inj : ∀ v (x : Lsq (Kv v) (cv v Δ)), (∀ w h, ρ v w h x = 0) → x = 0
  ρ_surj : ∀ v (a : Af L), ∃ x : Lsq (Kv v) (cv v Δ), ∀ w h, ρ v w h x = pLoc L w a
  ρ_int : ∀ v (x : Lsq (Kv v) (cv v Δ)), IsIntegral (Ov v) x ↔ ∀ w h, ρ v w h x ∈ w.adicCompletionIntegers L
  ρ_star : ∀ v (x : Lsq (Kv v) (cv v Δ)) (a : Af L), (∀ w h, ρ v w h x = pLoc L w a) → ∀ w h, ρ v w h (star x) = pLoc L w (cjF a)
  ρ_div : ∀ v w h (a : Kv v), ρ v w h (algebraMap _ _ a) ∈ w.adicCompletionIntegers L ↔ a ∈ v.adicCompletionIntegers (Lp L)

structure RingBr.Split (R : RingBr L) (w : Plc L) where
  s : Kv (un w)
  hs : s * s = cv (un w) R.Δ
  s_ne : s ≠ 0
  i : Kv (un w) ≃+* Kw w
  ρ_eq : ∀ x, R.ρ _ w rfl x = i (Sig.proj hs x)
  val_le : ∀ a b, valuation (Kw w) (i a) ≤ valuation (Kw w) (i b) ↔ valuation _ a ≤ valuation _ b
  abs : ∀ (z : ℂ) (a : (Kv (un w))ˣ), absPow (Kw w) z (Units.map (i : Kv (un w) →* Kw w) a) = absPow _ z a
  unif : valuation (Kw w) (i (Hi.unif (Kv (un w)) : Kv (un w))) = valuation (Kw w) (Hi.unif (Kw w) : Kw w)
  Uc : ∀ (c : ℕ) (a : (Kv (un w))ˣ), Units.map (i : Kv (un w) →* Kw w) a ∈ Hi.Uc (Kw w) c ↔ a ∈ Hi.Uc _ c
  Uo : ∀ a : (Kv (un w))ˣ, Units.map (i : Kv (un w) →* Kw w) a ∈ Hi.Uo (Kw w) ↔ a ∈ Hi.Uo _
  J : ∀ (V : Sig.Lev (Kv (un w))) (V' : Sig.Lev (Kw w)), V.c = V'.c →
    (∀ a, Units.map (i : Kv (un w) →* Kw w) a ∈ V'.H ↔ a ∈ V.H) →
    ∀ (n : ℕ) (g : GL (Fin n) (Kv (un w))), GeneralLinearGroup.map (i : Kv (un w) →+* Kw w) g ∈ V'.J n ↔ g ∈ V.J n
  K : ∀ (n : ℕ) (g : GL (Fin n) (Kv (un w))), GeneralLinearGroup.map (i : Kv (un w) →+* Kw w) g ∈ GlobalTheory.LFun.KGL w n ↔ g ∈ KO _ (Fin n)

variable (L) in

def SUA : Subgroup (UA L 2) := (GeneralLinearGroup.det.comp (UA L 2).subtype).ker

abbrev mL {n : ℕ} (w : Plc L) (x : UA L n) : Matrix (Fin n) (Fin n) (Kw w) := (cLoc w x : GL (Fin n) (Kw w))

variable (L) in

structure Bridge extends RingBr L where
  bG : GA Δ ≃* finU L 3
  bG_loc : ∀ g w, mL w (bG g : UA L 3) = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (ρ _ w rfl)
  bS : SA Δ ≃* ↥(finU L 2 ⊓ SUA L)
  bS_loc : ∀ g w, mL w (bS g : UA L 2) = (mt ((g : DA Δ).1 (un w))).map (ρ _ w rfl)
  rG : U3 Δ ≃* ratU L 3
  rG_loc : ∀ γ w, mL w (rG γ : UA L 3) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => algebraMap L (Kw w) (e x)
  rG_inf : ∀ γ (τ : L →+* ℂ), (cEmb τ (rG γ : UA L 3) : Matrix (Fin 3) (Fin 3) ℂ) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => τ (e x)
  rS : SU Δ ≃* ↥(ratU L 2 ⊓ SUA L)
  rS_loc : ∀ γ w, mL w (rS γ : UA L 2) = (mt (γ : DX Δ)).map fun x => algebraMap L (Kw w) (e x)
  rS_inf : ∀ γ (τ : L →+* ℂ), (cEmb τ (rS γ : UA L 2) : Matrix (Fin 2) (Fin 2) ℂ) = (mt (γ : DX Δ)).map fun x => τ (e x)

namespace Bridge

variable (B : Bridge L)

structure Ok : Prop where
  split : ∀ w, IsSplitAt w → Nonempty (B.toRingBr.Split w)
  chi : ∃ χ : ∀ v : Pl (Lp L), (Kv v)ˣ →* ℂˣ, ∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v B.Δ) → IsChi (Ov v) (cv v B.Δ) (χ v)
  finG : ∀ (γ : U3 B.Δ) (g : GA B.Δ),
    (∀ v, (g.1 v : Matrix (Fin 3) (Fin 3) _) = (γ : Matrix (Fin 3) (Fin 3) _).map (lmap (cv v) B.Δ)) →
    ∃ k ∈ infU L 3, (B.rG γ : UA L 3) = B.bG g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rG γ : UA L 3)
  finS : ∀ (γ : SU B.Δ) (g : SA B.Δ), (∀ v, mt ((g : DA B.Δ).1 v) = (mt (γ : DX B.Δ)).map (lmap (cv v) B.Δ)) →
    ∃ k ∈ infU L 2 ⊓ SUA L, (B.rS γ : UA L 2) = B.bS g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rS γ : UA L 2)
  KG : ∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w 3
  oneG : ∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1
  splG : ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ),
    cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w)))
  KS : ∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v ∈ KD _ (Ov v) ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) ∈ GlobalTheory.LFun.KGL w 2
  oneS : ∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) = 1
  splS : ∀ w (S : B.toRingBr.Split w) (g : SA B.Δ),
    cLoc w (B.bS g : UA L 2) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eD S.hs ((g : DA B.Δ).1 (un w)))
  conj : ∀ x ∈ finU L 2, ∃ y : DA B.Δ, (∀ v, (∀ w, un w = v → cLoc w x = 1) → y.1 v = 1) ∧
    ∀ g : SA B.Δ, ∃ g' : SA B.Δ, (g' : DA B.Δ) = y⁻¹ * g * y ∧ (B.bS g' : UA L 2) = x⁻¹ * B.bS g * x
  cong : ∀ (y : DA B.Δ) (m₀ : ℕ), m₀ ≠ 0 → ∃ m : ℕ, m ≠ 0 ∧ ∀ (g : SA B.Δ) (v : Pl (Lp L)),
    (∀ w, un w = v → ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w (B.bS g : UA L 2) - 1) i j = (m : Kw w) * a) →
    ∀ i j, ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA B.Δ).1 v) - 1) i j = (m₀ : Lsq (Kv v) (cv v B.Δ)) * a

end Bridge

def RingEx : Prop := ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → Nonempty (RingBr L)

def GroupEx : Prop := ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ B : Bridge L, B.toRingBr = R

def BridgeEx : Prop := ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∃ B : Bridge L, B.Ok

def UAFacts : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ),
    (∀ w : Plc L, IsSplitAt w → (∀ g, secW n w g ∈ locU n w) ∧ (∀ g, cLoc w (secW n w g) = g) ∧ Continuous (secW (L := L) n w) ∧
      ∀ x ∈ locU n w, x = secW n w (cLoc w x)) ∧
    (∀ (w : Plc L), ∀ x ∈ locU n w, ∀ y : UA L n, (∀ u, un u = un w → cLoc u y = 1) → Commute x y) ∧
    (∀ x : UA L n, ∃ f ∈ finU L n, ∃ k ∈ infU L n, x = f * k) ∧
    (∀ f ∈ finU L n, ∀ k ∈ infU L n, Commute f k) ∧
    (∀ x y : UA L n, (∀ w, cLoc w x = cLoc w y) → (∀ τ, cEmb τ x = cEmb τ y) → x = y) ∧
    (∀ x : UA L n, (x ∈ finU L n ↔ ∀ τ, cEmb τ x = 1) ∧ (x ∈ infU L n ↔ ∀ w, cLoc w x = 1)) ∧
    (∀ (w : Plc L), ∀ x ∈ finU L n, ∃ a ∈ locU n w, ∀ u, un u = un w → cLoc u a = cLoc u x) ∧
    ∀ w : Plc L, IsSplitAt w → ∀ x : UA L n, cLoc w x ∈ GlobalTheory.LFun.KGL w n → ∀ u, un u = un w → cLoc u x ∈ GlobalTheory.LFun.KGL u n

end UpperTheory.V.Z.Sym.Dict.Br

end
