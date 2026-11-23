import Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleStabilisersOfCompatibleForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.PUpNat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem translate_mem_span_adelic (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) {h : Frames (gramC J emb) → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range g)) :
    (fun y => (S.chi κ : ℂ) * h (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) ∈
      Submodule.span ℂ (Set.range g) := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨z, rfl⟩ := hh
    have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      Formalism.UG.Final.RatPtsLe F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩
    have hk : κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq κ.1).1 κ.2).1
    let z' : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * z.1 * κ.1, mul_mem (mul_mem hb z.2) hk⟩
    apply Submodule.subset_span
    refine ⟨z', ?_⟩
    funext y
    exact adelic_value_translate S emb hc hg γ hγ z z' κ rfl y
  | zero =>
    have e : (fun y => (S.chi κ : ℂ) * (0 : Frames (gramC J emb) → ℂ)
        (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) = 0 := by funext y; simp
    rw [e]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun y => (S.chi κ : ℂ) * (a + b) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) +
        (fun y => (S.chi κ : ℂ) * b (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp [mul_add]
    rw [e]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : (fun y => (S.chi κ : ℂ) * (r • a) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        r • (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact Submodule.smul_mem _ r ha

set_option maxHeartbeats 1000000 in

theorem adelic_function_extends_from_classes (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n)
    {C : Type} [Fintype C] (y : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : ∀ c, RndStabTriv S (y c))
    (hdis : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 = (y c').1 * κ.1 → c = c')
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdForms S emb lam)
    (Fc : C → Frames (gramC J emb) → ℂ) (hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g)) :
    ∃ G ∈ AdForms S emb lam, ∀ c, G (y c) = Fc c := by
  classical
  have hgA := (Submodule.mem_inf.1 hg).1
  have hgV : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) z trivial
  have hspan : Submodule.span ℂ (Set.range g) ≤ ValC (gramC J emb) lam :=
    Submodule.span_le.2 (by rintro _ ⟨z, rfl⟩; exact hgV z)
  let G := ∑ c, rndFillG S emb hc (y c) (Fc c)
  refine ⟨G, Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun c _ => rnd_fill_mem S emb hc (y c) (hs c) (Fc c), ?_⟩, ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => ?_
    show (∑ c, rndFillG S emb hc (y c) (Fc c)) x ∈ _
    rw [Finset.sum_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * (y c).1 * p.2.1
    · have e : rndFillG S emb hc (y c) (Fc c) x = fun yy => (S.chi (Classical.choose hx).2 : ℂ) *
          Fc c (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) yy) := by
        funext yy; unfold rndFillG; rw [dif_pos hx]
      rw [e]
      exact hspan (translate_mem_span_adelic S emb hc hgA _ (Classical.choose hx).1.2 _ (hF c))
    · have e : rndFillG S emb hc (y c) (Fc c) x = 0 := by
        funext yy; unfold rndFillG; rw [dif_neg hx]; rfl
      rw [e]; exact zero_mem _
  · intro c
    show (∑ c', rndFillG S emb hc (y c') (Fc c')) (y c) = Fc c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · exact rnd_fill_at S emb hc (y c) (hs c) (Fc c)
    · intro c' _ hne
      funext yy
      unfold rndFillG
      rw [dif_neg]
      · rfl
      rintro ⟨p, hp⟩
      apply hne
      refine hdis c' c p.1.1 p.1.2 p.2⁻¹ ?_
      rw [hp, InvMemClass.coe_inv]; group
    · intro h; exact absurd (Finset.mem_univ c) h

end Gen

section Tied

variable {D : D7} {u : D.what₂.Word}

theorem trivial_stabiliser_level_zero (Tf : FormsTied D u) (x0 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    RndStabTriv (Tf.cls 0 (Nat.zero_le _)).lev x0 := by
  intro δ hδ κ h
  apply adms_core Tf x0 δ hδ
  have e : x0.1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * x0.1 = κ.1 := by
    rw [mul_assoc, h]; group
  rw [e]; exact κ.2

theorem class_rep_unique_of_translate (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : (Tf.cls i hi).lev.U)
    (h : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((Tf.cls i hi).y c).1 =
      ((Tf.cls i hi).y c').1 * κ.1) : c = c' :=
  (Tf.cls i hi).y_bij.1 (rnd_cls _ γ hγ _ _ κ h)

set_option maxHeartbeats 4000000 in

theorem U_op_preserves_forms_level_zero (Tf : FormsTied D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : (D.fm u).lv 0 v c), (D.fm u).fv 0 v c x = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).upT 0 v c x (φ ((D.fm u).up 0 v c x)) = fun s => g p ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c x hx
    obtain ⟨z, rfl⟩ := (Tf.lv 0 (Nat.zero_le _)).pr_surj v c x
    obtain ⟨γ, η, κ, -, hrel, -, -, -, htr⟩ := upNat_of_tied Tf 0 (Nat.zero_le _) v c z hx
    refine ⟨(Tf.cls 0 (Nat.zero_le _)).y c * η, ?_⟩
    rw [htr, hgφ]
    exact natTr_adFun Tf 0 (Nat.zero_le _) hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1),
      if hx : (D.fm u).fv 0 v c x = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ c = fun s => Fc c ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Uop, Formalism.BasicNotions.LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    (Tf.cls 0 (Nat.zero_le _)).y (fun c => trivial_stabiliser_level_zero Tf _) (fun c c' γ hγ κ h => class_rep_unique_of_translate Tf 0 (Nat.zero_le _) c c' γ hγ κ h)
    hg Fc hF
  refine ((Tf.val 0 (Nat.zero_le _)).Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G ((Tf.cls 0 (Nat.zero_le _)).y c) z = _
  rw [hGc, hU]
  simp

set_option maxHeartbeats 4000000 in

theorem D_op_preserves_forms_level_zero (Tf : FormsTied D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), x ((D.fm u).te 0 v c) = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).dnT 0 v c x (φ ((D.fm u).dn 0 v c x)) = fun s => g p ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c x hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, LinearMap.zero_apply] at hx; exact zero_ne_one hx
    obtain ⟨γ, η, κ, -, hrel, -, -, htr⟩ := dnNat_of_tied Tf 0 (Nat.zero_le _) v c x hx0
    refine ⟨(Tf.cls 0 (Nat.zero_le _)).y c * η, ?_⟩
    rw [htr, hgφ]
    exact natTr_adFun Tf 0 (Nat.zero_le _) hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1),
      if hx : x ((D.fm u).te 0 v c) = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ c = fun s => Fc c ((Tf.val 0 (Nat.zero_le _)).eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    (Tf.cls 0 (Nat.zero_le _)).y (fun c => trivial_stabiliser_level_zero Tf _) (fun c c' γ hγ κ h => class_rep_unique_of_translate Tf 0 (Nat.zero_le _) c c' γ hγ κ h)
    hg Fc hF
  refine ((Tf.val 0 (Nat.zero_le _)).Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G ((Tf.cls 0 (Nat.zero_le _)).y c) z = _
  rw [hGc, hU]
  simp

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
