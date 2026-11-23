import Formalism.LocalToGlobal.Columns.TwQDefs
import Formalism.LocalToGlobal.Columns.MtHeckeKv
import Formalism.LocalToGlobal.Columns.RecLevelCls

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QSurj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

structure QOff : Prop where
  off : ∀ (P : Q) (P' : Pl E), P' ∈ ST ∨ P' ∈ SG → ¬ IsOver (qv F P.1) P'
  inj : ∀ P P' : Q, qv F P.1 = qv F P'.1 → P = P'

def QIntGL {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin n) (v.adicCompletion F)) : Prop :=
  (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F)

variable (ST SG) in

def FrLat (q : QLoc hc n Q Θ) : Prop :=
  ∀ (x : UAd hc n) (p : DecoF E n ST SG Q), decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco → ∀ P : Q,
    QIntGL ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)

def QLift (q : QLoc hc n Q Θ) : Prop :=
  ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)), QIntGL k →
    ∃ κ : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F),
      κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) ((qv F P.1).adicCompletion F) ∧
      κ ∈ stabGL (Formalism.L2.Herm.locL (qv F P.1) (stdLat E n)) ∧
      bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) κ = k

theorem qdf_at_put_ne (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : qv F P.1 ≠ v) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : q.at P (x * rll_put n v g) = q.at P x := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n v g)) = _
  rw [map_mul, rll_put_ne n v (qv F P.1) hv g, mul_one]

theorem qdf_at_put_self (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (g : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F)) :
    q.at P (x * rll_put n (qv F P.1) g) = q.at P x * bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) g := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n (qv F P.1) g)) = _
  rw [map_mul, rll_put_self, map_mul]

theorem qdf_inv_mem_UPts {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) :
    κ⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := inv_mem h

theorem qdf_inv_mem_stab {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : κ⁻¹ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := inv_mem h

theorem exists_adelic_point_of_local_frames (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q)
    (p : DecoF E n ST SG Q) (S : Finset Q) :
    ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco ∧
      ∀ P ∈ S, (bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ptOf hc n ST SG p.deco, decoOf_ptOf hc n ST SG hS p.deco, fun P hP => absurd hP (Finset.notMem_empty P)⟩
  | insert P S hPS ih =>
    obtain ⟨x, hx, hxS⟩ := ih
    obtain ⟨κ, hκU, hκS, hκ⟩ := hL P _ (hF x p hx P)
    have hput : rll_put n (qv F P.1) κ⁻¹ ∈ K1 hc n ST SG :=
      put_mem_kOne_of_not_over ST SG (fun P' hP' => hQ.off P P' (Or.inl hP'))
        (fun P' hP' => hQ.off P P' (Or.inr hP'))
        (rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)) (qdf_inv_mem_stab hκS)
    have hputU : rll_put n (qv F P.1) κ⁻¹ ∈ UAd hc n := rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)
    refine ⟨x * ⟨_, hputU⟩, ?_, ?_⟩
    · show decoOf ST SG ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) = _
      rw [decoration_mul_principal hc n ST SG _ hput, hx]
    · intro P' hP'
      show (bc (q.phi P') (qGL n (p.fr P')))⁻¹ * q.at P' ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) ∈ q.U P'
      rcases Finset.mem_insert.1 hP' with rfl | hP'
      · rw [qdf_at_put_self, map_inv, hκ, ← mul_assoc, mul_inv_cancel]
        exact one_mem _
      · have hne : qv F P'.1 ≠ qv F P.1 := fun h => hPS (hQ.inj P' P h ▸ hP')
        rw [qdf_at_put_ne q P' _ _ hne]
        exact hxS P' hP'

theorem decoPtSurjF_of (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q) :
    DecoPtSurjF hc n ST SG Q q := by
  classical
  intro p
  obtain ⟨x, hx, hxS⟩ := exists_adelic_point_of_local_frames hS hQ q hF hL p Finset.univ
  exact ⟨x, hx, fun P => hxS P (Finset.mem_univ P)⟩

end QSurj

end Formalism.L2.Col
