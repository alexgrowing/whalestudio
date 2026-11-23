import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

structure CGTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → Function.Surjective (e a)
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

def CGTrue.equiv {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T) (a : ℕ)
    (h : 0 < a) : D.naut.CG a ≃ HostCGu D.host a := Equiv.ofBijective (C.e a) ⟨(C.e a).injective, C.surj a h⟩

def wdCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) :
    GlobalTheory.RowTie.WDTie (setCG D hE K).nd (setCG D hE K).naut := { T with }

def cfCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (c : CharFrame D) : CharFrame (setCG D hE K) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

end GlobalTheory.HeightCounting

end
