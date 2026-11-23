import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem chi_mem_subfield {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t nb skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t nb skip fc zl) (K : Subfield ℂ) (hψ : ∀ i v h x, G.psi0 i v h x ∈ K)
    (hχ : ∀ i v h b, b < nb → ∀ x, G.chiB i v h b x ∈ K) (κ : S.U) : ((S.chi κ : ℂˣ) : ℂ) ∈ K := by
  rw [X.chi_eq κ]
  refine prod_mem fun i _ => ?_
  refine finprod_induction (fun z : ℂ => z ∈ K) (one_mem K) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => z ∈ K) (one_mem K) (fun _ _ hx hy => mul_mem hx hy) fun h => ?_
  refine inv_mem ?_
  unfold lamJ
  exact mul_mem (hψ i v h _) (prod_mem fun b hb => hχ i v h b (Finset.mem_range.1 hb) _)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem adExt_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    AdExt ((T u).cls0).lev (embT D) D.what₂.embLL (embFr T u) ((T u).cls0).y := by
  intro x
  have h1 : (D.fm u).emb 0 x ∈ (D.fm u).Fi 0 := ((((T u).val0).rat _).1 ⟨x, rfl⟩).1
  obtain ⟨fa, hfa, e⟩ := (((T u).val0).Fi _).1 h1
  exact ⟨fa, hfa.1, fun c => congrFun e c⟩

def LevelZeroCharacterRational (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Prop :=
  ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = (T u).gl.psi0 i v h x

theorem chiRatAll_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (h : LevelZeroCharacterRational T u) :
    ChiRatAll ((T u).cls0).lev D.what₂.embLL := by
  intro κ
  exact RingHom.mem_fieldRange.1 (chi_mem_subfield ((T u).glev0) D.what₂.embLL.fieldRange
    (fun i v hv x => RingHom.mem_fieldRange.2 (h i v hv x)) (fun _ _ _ b hb => absurd hb (Nat.not_lt_zero b)) κ)

variable {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 4000000 in

theorem ex_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hO : PtOne ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B))
    (h1 : EvRatRep (embT D) D.what₂.embLL (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u))
    (h2 : LevelZeroCharacterRational T u) :
    ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
      (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y :=
  valEx_of_rep' (tEL D) (tEL_emb D) (embT_conj D) (locAt_std u w hg I.B I.B_std) (adExt_rec T u)
    (ptEx_rec X T u w hg I.B) hO h1 (chiRatAll_rec T u h2)

end Formalism.L2.G
