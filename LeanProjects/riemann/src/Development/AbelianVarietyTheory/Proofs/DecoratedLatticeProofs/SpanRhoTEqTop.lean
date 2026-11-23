import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

open Formalism.UG (IsInertAt)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    w.adicCompletion D.host.E →+ AE D :=
  (GlobalTheory.EmbChart.tensAt D.host.E v).toAddMonoidHom.comp
    (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom.toAddMonoidHom

def uPt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E))
    (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) : WO S T :=
  (k • (aT.1 * x * (aS⁻¹).1)).map (secW hw h)

def thW (ψ : AddChar (AF D.host.F) ℂ) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (k : w.adicCompletion D.host.E) : AddChar (w.adicCompletion D.host.E) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (incA D D.host.xi0)).comp ((secW hw h).comp (AddMonoidHom.mulLeft k))))

variable {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
  {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
  {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}

theorem thW_apply (ψ : AddChar (AF D.host.F) ℂ) (z : w.adicCompletion D.host.E) :
    thW ψ hw h k z = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * secW hw h (k * z))) := rfl

theorem uPt_add (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := by
  ext i j
  simp [uPt, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem uPt_zero : uPt hw h k aS aT (0 : Matrix (Fin T.rank) (Fin S.rank) _) = 0 := by
  ext i j
  simp [uPt]

theorem infPart_tensAt (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) ⊗ₜ[D.host.F] x = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy, add_zero]

theorem infPart_secW (z : w.adicCompletion D.host.E) : infPart D (secW hw h z) = 0 :=
  infPart_tensAt _

theorem map_infPart_uPt (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    (uPt hw h k aS aT x).map (infPart D) = 0 := by
  ext i j
  exact infPart_secW _

section Anti

open Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

variable {L : Type} [Field L]

theorem antiJ_herm (σ : L →+* L) (n : ℕ) (i j : Fin n) : σ (antiJ L n i j) = antiJ L n j i := by
  simp only [antiJ]
  rw [show j.val + i.val = i.val + j.val from add_comm _ _]
  split_ifs <;> simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem antiG_mem (n : ℕ) : GlobalTheory.SphTheta.antiG L n ∈ GLint (Fin n) (intL L) := by
  let A : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hA : A.map (intL L).subtype = antiJ L n := by
    ext i j
    show ((if i.val + j.val + 1 = n then 1 else 0 : intL L) : L) = antiJ L n i j
    simp only [antiJ]
    split_ifs <;> simp
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intL L) => M.map (intL L).subtype :=
    fun M N e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
  have hAA : A * A = 1 := hinj (by
    show (A * A).map (intL L).subtype = (1 : Matrix (Fin n) (Fin n) (intL L)).map (intL L).subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA]
    exact P.fIwasawa_antiJ_mul_antiJ)
  exact ⟨⟨A, A, hAA, hAA⟩, Units.ext hA⟩

end Anti

section Build

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {X : Type} (u : X → WO S T) (f : WO S T → ℂ)

def spanT : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ (Set.range fun x => heisO ψ S T (u x) f)

variable {ψ u f}

theorem mem_spanT_of {g : Module.End ℂ (WO S T → ℂ)} (hg : ∀ x, g (heisO ψ S T (u x) f) ∈ spanT ψ u f) {m : WO S T → ℂ}
    (hm : m ∈ spanT ψ u f) : g m ∈ spanT ψ u f := by
  have key : spanT ψ u f ≤ (spanT ψ u f).comap g := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact hg x)
  exact key hm

theorem heis_mem_spanT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) {m : WO S T → ℂ} (hm : m ∈ spanT ψ u f) :
    heisO ψ S T (u x) m ∈ spanT ψ u f :=
  mem_spanT_of (g := GlobalTheory.SplitScalar.heisL ψ S T (u x)) (fun y => by
    show heisO ψ S T (u x) (heisO ψ S T (u y) f) ∈ spanT ψ u f
    rw [GlobalTheory.SplitScalar.heisO_heisO, ← hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)) hm

theorem self_mem_spanT [Zero X] (hu : u 0 = 0) : f ∈ spanT ψ u f :=
  Submodule.subset_span ⟨0, by
    show heisO ψ S T (u 0) f = f
    rw [hu, GlobalTheory.SplitScalar.heisO_zero]⟩

variable (ψ u f) in

def rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) : Module.End ℂ (spanT ψ u f) :=
  (GlobalTheory.SplitScalar.heisL ψ S T (u x)).restrict fun _ hm => heis_mem_spanT hu x hm

theorem coe_rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) (m : spanT ψ u f) :
    (rhoT ψ u f hu x m : WO S T → ℂ) = heisO ψ S T (u x) m := rfl

variable (ψ u f) in

def omT {G : Type} [Monoid G] (π : G →* Module.End ℂ (WO S T → ℂ))
    (hπ : ∀ g, ∀ m ∈ spanT ψ u f, π g m ∈ spanT ψ u f) : G →* Module.End ℂ (spanT ψ u f) where
  toFun g := (π g).restrict (hπ g)
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show π 1 m = m
    rw [map_one, Module.End.one_apply])
  map_mul' g g' := LinearMap.ext fun m => Subtype.ext (by
    show π (g * g') m = π g (π g' m)
    rw [map_mul, Module.End.mul_apply])

theorem span_rhoT_eq_top [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (hf : f ∈ spanT ψ u f) :
    Submodule.span ℂ (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) = ⊤ := by
  have e : (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) =
      ((↑) : spanT ψ u f → WO S T → ℂ) ⁻¹' Set.range fun x => heisO ψ S T (u x) f := by
    ext m
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [e]
  exact Submodule.span_span_coe_preimage

end Build

end GlobalTheory.InertFrameLoc

end
