import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite

open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K) in

theorem exists_natCast_mul_mem_of_mem_nhds {W : Set (FiniteAdeleRing (𝓞 K) K)}
    (hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      (M : FiniteAdeleRing (𝓞 K) K) * a ∈ W := by
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 K) K
  have hO : IsCompact (O : Set (FiniteAdeleRing (𝓞 K) K)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles K
  set N := {c : FiniteAdeleRing (𝓞 K) K | ∀ a ∈ (O : Set (FiniteAdeleRing (𝓞 K) K)), c * a ∈ W}
  have hN : N ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have h := (continuous_mul (M := FiniteAdeleRing (𝓞 K) K)).tendsto ((0 : FiniteAdeleRing (𝓞 K) K), a)
    rw [zero_mul] at h
    exact h hW
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hN
  set V' := V ∩ (fun v => -v) ⁻¹' V
  have hV' : V' ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := by
    refine inter_mem hV ?_
    have := (continuous_neg (G := FiniteAdeleRing (𝓞 K) K)).tendsto 0
    rw [neg_zero] at this
    exact this hV
  have hsub : ∀ v ∈ V', ∀ w ∈ V', v - w ∈ N := fun v hv w hw => by
    rw [sub_eq_add_neg]
    exact hVV v hv.1 (-w) hw.2
  obtain ⟨t, -, hcover⟩ := hO.elim_nhds_subcover (fun c => {y | y - c ∈ V'}) fun c _ => by
    have := (continuous_sub_right c).tendsto c
    rw [sub_self] at this
    exact this hV'
  have hmem : ∀ j : ℕ, ∃ c : t, (j : FiniteAdeleRing (𝓞 K) K) - c ∈ V' := by
    intro j
    have hj : (j : FiniteAdeleRing (𝓞 K) K) ∈ (O : Set (FiniteAdeleRing (𝓞 K) K)) :=
      natCast_mem O j
    obtain ⟨c, hc, hjc⟩ := mem_iUnion₂.1 (hcover hj)
    exact ⟨⟨c, hc⟩, hjc⟩
  choose f hf using hmem
  obtain ⟨j, j', hne, hjj⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (t.card + 1) => f i) (by simp)
  have key : ∀ i i' : Fin (t.card + 1), f i = f i' →
      ((i : ℕ) : FiniteAdeleRing (𝓞 K) K) - (i' : ℕ) ∈ N := by
    intro i i' h
    have h1 := hf i
    have h2 := hf i'
    rw [h] at h1
    have := hsub _ h1 _ h2
    rwa [sub_sub_sub_cancel_right] at this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(j' : ℕ) - j, Nat.sub_pos_of_lt hlt, fun a ha => ?_⟩
    rw [Nat.cast_sub hlt.le]
    exact key j' j hjj.symm a ha
  · refine ⟨(j : ℕ) - j', Nat.sub_pos_of_lt hlt, fun a ha => ?_⟩
    rw [Nat.cast_sub hlt.le]
    exact key j j' hjj a ha

theorem continuous_unipMatrix' {r : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    Continuous (unipMatrix : (UPos n r → R) → Matrix (Fin n) (Fin n) R) := by
  refine continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unipGL' {r : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (unipGL : (UPos n r → R) → GL (Fin n) R) :=
  Units.continuous_iff.2 ⟨continuous_unipMatrix', continuous_unipMatrix'.comp continuous_neg⟩

theorem adele_add_fst (p q : 𝔸[K]) : (p + q).1 = p.1 + q.1 := rfl

theorem adele_add_snd (p q : 𝔸[K]) : (p + q).2 = p.2 + q.2 := rfl

theorem adele_one_fst : (1 : 𝔸[K]).1 = 1 := rfl

theorem adele_one_snd : (1 : 𝔸[K]).2 = 1 := rfl

theorem adele_zero_fst : (0 : 𝔸[K]).1 = 0 := rfl

theorem adele_zero_snd : (0 : 𝔸[K]).2 = 0 := rfl

theorem prodEquiv_unipGL_fst {r : ℕ} (z : UPos n r → 𝔸[K]) (hz : ∀ p, (z p).1 = 0) :
    (AdelicGLn.prodEquiv K n (unipGL z)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_fst, coe_unipGL, Units.val_one]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rw [adele_add_fst]
  split_ifs with h1 h2 h2
  · rw [hz, adele_one_fst, add_zero]
  · rw [adele_one_fst, adele_zero_fst, add_zero]
  · rw [hz, adele_zero_fst, add_zero]
  · rw [adele_zero_fst, add_zero]

theorem prodEquiv_unipGL_snd {r : ℕ} (z : UPos n r → 𝔸[K]) :
    (AdelicGLn.prodEquiv K n (unipGL z)).2 = unipGL fun p => (z p).2 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_unipGL, coe_unipGL]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rw [adele_add_snd]
  split_ifs with h1 h2 h2
  · rw [adele_one_snd]
  · rw [adele_one_snd, adele_zero_snd]
  · rw [adele_zero_snd]
  · rw [adele_zero_snd]

theorem exists_natCast_conj_unipGL_mem (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) {ω : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ k ∈ (maxCompact (K := K) (n := n)), ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
        (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
          (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
        ∃ u : U, ((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k)⁻¹ :
            AdelicGLn.AdelicGL K n) * unipGL z * (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k) =
          finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := by
  classical

  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))
  have hU' : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U' := ⟨1, U.one_mem, rfl⟩

  set Cf : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n (p.1 * p.2)).2) ''
      (ω ×ˢ (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)))
  have hCf : IsCompact Cf := (hω.prod isCompact_maxCompact).image
    (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp (continuous_fst.mul continuous_snd)))

  have hcont : Continuous fun q : (UPos n r → FiniteAdeleRing (𝓞 K) K) × AdelicGLn.FiniteAdelicGL K n =>
      q.2⁻¹ * unipGL q.1 * q.2 :=
    (continuous_snd.inv.mul (continuous_unipGL'.comp continuous_fst)).mul continuous_snd
  have hev : ∀ᶠ w in 𝓝 (0 : UPos n r → FiniteAdeleRing (𝓞 K) K), ∀ c ∈ Cf,
      c⁻¹ * unipGL w * c ∈ U' := by
    refine hCf.eventually_forall_of_forall_eventually fun c _ => ?_
    refine (hcont.tendsto ((0 : UPos n r → FiniteAdeleRing (𝓞 K) K), c)).eventually
      (hU'.mem_nhds ?_)
    simp only [unipGL_zero, mul_one, inv_mul_cancel]
    exact h1U'
  rw [nhds_pi] at hev
  have hev' : {w : UPos n r → FiniteAdeleRing (𝓞 K) K | ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'} ∈
      Filter.pi fun _ => 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := hev
  rw [Filter.mem_pi] at hev'
  obtain ⟨I, -, tt, htt, hIt⟩ := hev'
  obtain ⟨M, hM, hMW⟩ := exists_natCast_mul_mem_of_mem_nhds K (Filter.iInter_mem.2 htt)
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  set w : UPos n r → FiniteAdeleRing (𝓞 K) K := fun p => (z p).2
  have hw : w ∈ I.pi tt := fun p _ => by
    obtain ⟨a, ha, hza⟩ := hz2 p
    have := hMW a ha
    rw [mem_iInter] at this
    change (z p).2 ∈ tt p
    rw [hza]
    exact this p
  set c := (AdelicGLn.prodEquiv K n (b * k)).2
  have hc : c ∈ Cf := ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  obtain ⟨u, huU, hu⟩ := hIt hw c hc
  refine ⟨⟨u, huU⟩, ?_⟩
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv,
      prodEquiv_unipGL_fst z hz1, mul_one, inv_mul_cancel]
  · change _ = (u : AdelicGLn.FiniteAdelicGL K n)
    rw [hu, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv,
      prodEquiv_unipGL_snd]
    simp only [c, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd ρ hρ, mul_one]
    rfl

end CuspidalSpectrum

end

end GroundTheory.Automorphic
