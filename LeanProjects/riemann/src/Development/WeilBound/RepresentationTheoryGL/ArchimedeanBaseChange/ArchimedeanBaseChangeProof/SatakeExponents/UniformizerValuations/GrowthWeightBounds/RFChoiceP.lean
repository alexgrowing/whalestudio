import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.GrowthPiAt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RF_same {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  d.S₀ = F₀.d₀.S₀ ∧ d.Bad = F₀.d₀.Bad ∧ d.μ = F₀.d₀.μ ∧ d.ϖ = F₀.d₀.ϖ ∧ d.K' = F₀.d₀.K' ∧ d.X = F₀.d₀.X ∧
  d.L = F₀.d₀.L ∧ d.fix = F₀.d₀.fix ∧ d.KB = F₀.d₀.KB

def RF_T_in {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (Z : Finset (Pl E)) (βx : Pl E → Fin (n / 2) → ℂˣ) : Prop :=
  ∀ w ∈ d.T, w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ w ∉ Z ∧ IsWitt n w (d.b w) ∧ IsExtOf2 π w (βx w)

def valU (d : LocData E n) (w : Pl E) (β : Fin (n / 2) → ℂˣ) : ℂ := (d.c w).sum fun x t => t * (dlt n w (lOf x) * pw β (lOf x))

def valG (d : LocData E n) (a : ℕ) (w : Pl E) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (ξa : Fin a → ℂˣ)
    (ξb : Fin (n - a) → ℂˣ) : ℂ :=
  (d.c w).sum fun x t => t * (-qh w) ^ (-vRes n a (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)

def RF_choiceT {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ d.T, ∀ s (h : LocData.admitted n (F₀.C.a i) s) ξa ξb,
  JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → valG d _ w s h ξa ξb ≠ 0 → N3.Mono ξa ∧ N3.Mono ξb ∧ (CG.mk π).HasSat w
    ((Finset.univ.val.map ξa).map (· * (F₀.μ ^ (n - F₀.C.a i)).val w) + (Finset.univ.val.map ξb).map (· * (F₀.μ ^ F₀.C.a i).val w))

def RF_choiceM {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ d.T, Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m

def RF_choiceP {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) (βx : Pl E → Fin (n / 2) → ℂˣ) :
    Prop :=
  ∀ (Pa : Pre E (F₀.C.a F₀.i₀)) (Pb : Pre E (n - F₀.C.a F₀.i₀)), IsOne Pa F₀.π' → Pb.c = 0 → ∀ w ∈ d.T,
    Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 _ _ w)) ≤ m ∧ ∀ s (h : LocData.admitted n (F₀.C.a F₀.i₀) s) ξb, ∃ ξ,
      N3.Mono ξ ∧ (∀ x : Fin n → ℤ, pw ξ (restr x _ h.2.1) = pw (βx w) (lOf x)) ∧ JEig Pa Pb w (F₀.d₀.ϖ w) ξ ξb ∧
        valG d _ w s h ξ ξb = 1 ∧ ∀ ξ', JEig Pa Pb w (F₀.d₀.ϖ w) ξ' ξb → valG d _ w s h ξ' ξb ≠ 0 → ξ' = ξ

def RF_eP {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  ∀ w ∈ d.S₀, ∃ v₀ ∈ fixed (F₀.τ w).ρ (d.K' w), ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed (F₀.τ w).ρ (d.K' w),
    hk (F₀.τ w).ρ (d.K' w) (d.e w) v = (((d.K' w).relIndex (GlobalTheory.LFun.KGL w n) : ℕ) : ℂ) • l v • v₀

def RF_choiceU {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) (βx : Pl E → Fin (n / 2) → ℂˣ) (fam : U.UFam F₀.Sec F₀.lam d.KU) : Prop :=
  ∀ j : fam.ι, (∀ w ∈ d.S₀, locOp (fam.σ j w) (d.KU w) (d.g₀ w) ≠ 0 → Comp (fam.π j) w (F₀.τ w)) ∧
    ∀ w ∈ d.T, Module.finrank ℂ ↥(fixed (fam.σ j w).ρ (d.KU w)) ≤ m ∧ ∀ β : Fin (n / 2) → ℂˣ,
      (∃ y ∈ fixed (fam.σ j w).ρ (iwU n w (d.b w)), y ≠ 0 ∧ ∀ l : Fin (n / 2) → ℤ, Cone l →
        levOp (fam.σ j w).ρ (KL n w) (iwU n w (d.b w)) (fU n w (d.b w) (d.ϖ w) l) LinearMap.id y =
          ((((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * dlt n w l * pw β l) • y) → valU d w β ≠ 0 → β = βx w

def DOut {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (D : Pre E n) : Prop :=
  (∀ v : InfinitePlace E, ∑ i, D.m i v.embedding = infOfWeight (F₀.lam v)) ∧
  (∀ τ m, π.HasInfChar τ m → ∑ i, D.m i τ = m) ∧ SplitLike D π ∧
  (∀ w ∈ d.T, ∀ B, (CG.mk π).HasSat w B → D.Sat w B) ∧ (∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (F₀.K w)) ∧
  ∀ i, HasKType (F₀.W (D.N i)) (D.V i)

def RF_sep {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop := ∀ D : Pre E n, DOut F₀ d D → IsOne D π

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RunFrame {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (Z T₀ : Finset (Pl E)) : Type 1 where
  d : LocData E n
  same : RF_same F₀ d
  m : ℕ
  m_pos : 1 ≤ m
  ok : d.Ok
  mok : MLM.MOk d
  T_ne : d.T.Nonempty
  T_sup : T₀ ⊆ d.T
  βx : Pl E → Fin (n / 2) → ℂˣ
  T_in : RF_T_in F₀ d Z βx
  levOff : U.LevelOff F₀.Sec d.B d.KU
  fam : U.UFam F₀.Sec F₀.lam d.KU
  R : U.UMod fam d.B (d.gU m)
  choiceT : RF_choiceT F₀ d
  choiceM : RF_choiceM F₀ d m
  choiceP : RF_choiceP F₀ d m βx
  eP : RF_eP F₀ d
  choiceU : RF_choiceU F₀ d m βx fam
  sep : RF_sep F₀ d

end PositivityTheory.Rg.BcB.F.FrE

end
