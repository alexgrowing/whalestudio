import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.RecLevelAsm

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl)

section QDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (Pl E))

variable (F) in

abbrev qv (P : Pl E) : HeightOneSpectrum (𝓞 F) := underPl F P

abbrev qGL (g : Sp E n ≃ₗ[E] Sp E n) : GL (Fin n) E := toGLm E n g

instance qdAct {K : Type} [Field K] (H : Subgroup (GLG E n SG)) (Θ : LevQFam E K n Q) :
    MulAction (UF E n × H × Θ.grp) (DecoF E n ST SG Q) :=
  MulAction.compHom _ (MonoidHom.prodMap (MonoidHom.id _) (MonoidHom.prodMap H.subtype Θ.grp.subtype))

structure QLoc {K : Type} [Field K] (Θ : LevQFam E K n Q) where
  sp : ∀ P : Q, E ⊗[F] (qv F P.1).adicCompletion F ≃+* (qv F P.1).adicCompletion F × (qv F P.1).adicCompletion F
  sp_sig : ∀ P x, sp P (Formalism.UG.sigR hc.sig ((qv F P.1).adicCompletion F) x) = Formalism.UG.swapR _ (sp P x)
  sp_alg : ∀ P (a : (qv F P.1).adicCompletion F), sp P ((1 : E) ⊗ₜ[F] a) = (a, a)

  sp_int : ∀ (P : Q) (x : E ⊗[F] (qv F P.1).adicCompletion F), x ∈ Formalism.BasicNotions.intV E (qv F P.1) ↔
    (sp P x).1 ∈ (qv F P.1).adicCompletionIntegers F ∧ (sp P x).2 ∈ (qv F P.1).adicCompletionIntegers F

  sp_P : ∀ (P : Q) (r : 𝓞 E), Valued.v (sp P (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E))).1 < 1 ↔ r ∈ P.1.asIdeal

  U : ∀ P : Q, Subgroup (GL (Fin n) ((qv F P.1).adicCompletion F))
  U_int : ∀ P : Q, ∀ k ∈ U P, ∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F

  U_rat : ∀ (P : Q) (g : GLint E n P.1),
    Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P ↔
      g ∈ (Θ P).H

  U_dense : ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)),
    (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    ∃ g : GLint E n P.1,
      (Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1))⁻¹ * k ∈ U P
  chr : ∀ P : Q, U P →* Kˣ
  chr_rat : ∀ (P : Q) (g : GLint E n P.1) (hg : g ∈ (Θ P).H)
    (h : Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P),
    chr P ⟨_, h⟩ = (Θ P).lam ⟨g, hg⟩

variable {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable {hc n Q} in

abbrev QLoc.phi (q : QLoc hc n Q Θ) (P : Q) : E →+* (qv F P.1).adicCompletion F :=
  (RingHom.fst _ _).comp ((q.sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))

variable {hc n Q} in

abbrev QLoc.at (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin n) ((qv F P.1).adicCompletion F) :=
  Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1)) x)

def levUQ (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  levU hc n ST SG H ⊓ ⨅ P : Q, (q.U P).comap ((Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom)).comp
    (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1))))

variable {hc n ST SG Q}

def FrOver (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, (Formalism.UG.bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P

variable (hc n ST SG Q)

def DecoPtSurjF (q : QLoc hc n Q Θ) : Prop := ∀ p : DecoF E n ST SG Q, ∃ x : UAd hc n, FrOver q x.1 p

def ptOfF (q : QLoc hc n Q Θ) (p : DecoF E n ST SG Q) : UAd hc n :=
  open Classical in if h : ∃ x : UAd hc n, FrOver q x.1 p then h.choose else 1

abbrev DecoFCl (H : Subgroup (GLG E n SG)) (Θ' : LevQFam E K n Q) : Type :=
  MulAction.orbitRel.Quotient (UF E n × H × Θ'.grp) (DecoF E n ST SG Q)

abbrev RecClsF (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) : Type :=
  RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levUQ hc n ST SG Q H q)
    (fun c => MulAction.stabilizer (UF E n × H × Θ.grp) (s c)) (fun c => (s c).deco.1.L)

end QDict

end Formalism.L2.Col
