import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.RowRead

theorem map_mem_span_range {K L M N J : Type*} [Semiring K] [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M]
    [Module L N] {σ : K →+* L} (f : M →ₛₗ[σ] N) {φ : J → M} (h : Submodule.span K (Set.range φ) = ⊤) (z : M) :
    f z ∈ Submodule.span L (Set.range fun a => f (φ a)) := by
  have hz : z ∈ Submodule.span K (Set.range φ) := h ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

def valMt (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) :
    (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun F p := F.1 () p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def valMtP : MtP W Ch sel mu P σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun G p := G.1 (toRow sel mu p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valMtP_injective : Function.Injective (valMtP W Ch sel mu P σ) := by
  intro G G' h
  refine Subtype.ext (funext fun d => ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  exact congrFun h (trivPt X _ _ _ _ p)

theorem rowEmb_linearIndependent (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) {J : Type} {φ : J → MtildeV W Ch sel mu P}
    (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun a => rowEmb W Ch sel mu P b0 til ext tz H hd σ (φ a) :=
  LinearIndependent.of_comp (valMt W Ch sel mu P b0 til ext tz σ H)
    ((toMtilde_linearIndependent W Ch sel mu P σ h).map' (valMtP W Ch sel mu P σ)
      (LinearMap.ker_eq_bot.2 (valMtP_injective W Ch sel mu P σ)))

theorem rowEmb_span (hX : X.Ok) {J : Type} {φ : J → MtildeV W Ch sel mu P} (h : Submodule.span X.K (Set.range φ) = ⊤) :
    Submodule.span ℂ (Set.range fun a => rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ (φ a)) = ⊤ :=
  GlobalTheory.PerQ.RowIntModel.eq_top_of_rowEmb_mem W Ch sel mu P b0 til ext tz hd σ hX _ fun z _ =>
    map_mem_span_range (rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ) h z

end G

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_reference_twist_primes (h : I.Ok) :
    Disjoint (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) :=
  Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I I.mu0) (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1

def rowRead (h : I.Ok) (l : I.Laws) (u : B.Word) : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt :=
  GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H (disjoint_reference_twist_primes I h) B.embLL

end GlobalTheory.Core.Rk.RowRead

end
