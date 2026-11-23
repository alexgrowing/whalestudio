import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

abbrev RowSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cX : CoefA D.sp.X') (pl : Pl0 → Pl D.host.E) (t : T) : Type :=
  Bridge.SideReal D D.sp.X' (Bridge.envOf cX.coef (levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t)))
    (A3.A.MtildeCSD t) (A3.A.leftGroupActionRight t) (A3.A.heckeR t) (fun i => i.2)

abbrev LiftSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (i : Fin D.R.m) (t : T) : Type :=
  Bridge.SideReal D (Vc D i) (Bridge.envOf (cV i).coef (levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t)))
    (A3.A.MtCSD i t) (A3.A.leftGroupActionLift i t) (A3.A.heckeL i t) (fun i => i.2)

open Classical in

def PrIso {D : D7} (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : D.what₂.Tau → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (MX.sm τ)) (w w' : cX.W),
    inner ℂ w w' = ∑ f : (∀ τ, ι τ),
      starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * prX w' (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

theorem brgAt_of_sides (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T)
    (h : ∀ eG : G ≃* Formalism.L2.DIV.G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ →
      ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
      ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (plI : I0 → Pl D.host.E)
        (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
        (RS : ∀ t, Set (RowSideT A3 L cX pl t)) (LS : ∀ i t, Set (LiftSideT A3 L cV pl i t)),
        cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ (∀ t, (RS t).Nonempty) ∧ (∀ i t, (LS i t).Nonempty) ∧
        (D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t ∧ ∀ i : Fin D.R.m, (Vc D i).rank = A3.A.r + A3.A.t) ∧
        ∀ B : BType A3 L cX cV pl, (∀ t, B.R t ∈ RS t) → (∀ i t, B.L i t ∈ LS i t) → BrgL A3 L eG cX cV pl Sb B plI SF) :
    BrgAt A3 L := by
  unfold BrgAt
  intro eG hrec θ hθ MX
  obtain ⟨cX, cV, pl, Sb, plI, SF, prX, RS, LS, hcX, hcV, hdual, hRS, hLS, hrk, hB⟩ := h eG hrec θ hθ MX
  refine ⟨cX, cV, pl, Sb, ⟨fun t => (hRS t).some, fun i t => (hLS i t).some, hrk.1, hrk.2⟩, plI, SF, prX, hcX, hcV, hdual, ?_⟩
  exact hB _ (fun t => (hRS t).some_mem) (fun i t => (hLS i t).some_mem)

theorem brgAtP_of_sides (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T)
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (_cv : ∀ i, CoefA (Vc D i)), (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop)
    (h : ∀ eG : G ≃* Formalism.L2.DIV.G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ →
      ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
      ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (plI : I0 → Pl D.host.E)
        (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
        (RS : ∀ t, Set (RowSideT A3 L cX pl t)) (LS : ∀ i t, Set (LiftSideT A3 L cV pl i t)),
        cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Pr MX cX cV prX ∧ (∀ t, (RS t).Nonempty) ∧ (∀ i t, (LS i t).Nonempty) ∧
        (D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t ∧ ∀ i : Fin D.R.m, (Vc D i).rank = A3.A.r + A3.A.t) ∧
        ∀ B : BType A3 L cX cV pl, (∀ t, B.R t ∈ RS t) → (∀ i t, B.L i t ∈ LS i t) → BrgL A3 L eG cX cV pl Sb B plI SF) :
    BrgAtP A3 L Pr := by
  unfold BrgAtP
  intro eG hrec θ hθ MX
  obtain ⟨cX, cV, pl, Sb, plI, SF, prX, RS, LS, hcX, hcV, hdual, hPr, hRS, hLS, hrk, hB⟩ := h eG hrec θ hθ MX
  refine ⟨cX, cV, pl, Sb, ⟨fun t => (hRS t).some, fun i t => (hLS i t).some, hrk.1, hrk.2⟩, plI, SF, prX, hcX, hcV, hdual, hPr, ?_⟩
  exact hB _ (fun t => (hRS t).some_mem) (fun i t => (hLS i t).some_mem)

end Formalism.IndefR.Seed
