import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))

theorem killFin (hU : Unimod) (hT : ThetaBasic) (hP : PureAct) (hL : LocCpt) (hp : IsPair B M χX χW om r s r' s') {𝓒}
    (hc : Cls B M om 𝓒) (v : Pl F) (adm : AdmAt om v) {N}
    (hN : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N)
    (hu : ∀ N', Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N' → N' = N)
    {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    (h𝓒 : ∀ x ∈ SB _, pure f (upd φ v x) ∈ 𝓒) (hv : φ v ∈ N) : M.I om (pure f φ) = 0 := by
  classical
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one hP hp f h1 h2 v
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  obtain ⟨hΓ, μ, 𝓕, hμ, h𝓕, hr⟩ := uniW hU hp
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨hinv, hmul, hcpt⟩ := hL F E σ d W v
  have o1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]
  have o2 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by simp [mat]
  let Q := SB (Fin n × Fin d → Fv F v)
  have jc : ∀ x : Q, j x ∈ 𝓒 := fun x => hj x ▸ h𝓒 x x.2
  let u : Q →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun x => M.I om (j x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add, I_add' hp hc (jc x) (jc y)]
      map_smul' := fun c x => funext fun h => by
        rw [Submodule.coe_smul, map_smul]; exact PositivityTheory.ThKG.I_smul M om c _ h }
  have hu' : ∀ x, u x = M.I om (j x) := fun _ => rfl
  have uc : ∀ x, Continuous (u x) := fun x => hc.cont _ (jc x)
  have u2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ := fun x => hc.sq μ 𝓕 hμ h𝓕 _ (jc x)
    (hj x ▸ Submodule.subset_span ⟨f, hf, _, upd_sb h1 x.2, upd_cof h2 v x, rfl⟩)
  have ui : ∀ x, L2.Inv (ratU σ W.J) (u x) := fun x => I_inv hT hp (hc.sch (jc x))
  obtain ⟨β, hβ, hs, hpos⟩ := exists_beta 𝓕 μ u uc u2
  let A : ∀ h ∈ UAt σ W (evFin F v), Module.End ℂ Q := fun h hh => (ω (1, h)).restrict (hω.pres 1 o1 h hh)
  have hA : ∀ h hh (x : Q), (A h hh x : _ → ℂ) = ω (1, h) x := fun _ _ _ => rfl
  have uA : ∀ h hh x g, u (A h hh x) g = u x (g * h) := fun h hh x g => by
    rw [hu', hu', hA h hh, ← hjS (om (1, h)) x x.2 _ ((hω.acts 1 o1 h hh x x.2 _).2 rfl), I_right]
  have iso : ∀ h hh x y, β (A h hh x) (A h hh y) = β x y := fun h hh x y => by
    simp only [hβ, uA]; exact L2.form_right h𝓕 (ui x) (ui y) h
  have Amul : ∀ h hh h' hh' x, A (h * h') (hmul h hh h' hh') x = A h hh (A h' hh' x) := fun h hh h' hh' x =>
    Subtype.ext (by
      have := hω.mul 1 o1 h hh 1 o1 h' hh' x x.2
      rw [mul_one] at this
      exact this)
  have Aone : ∀ x, A 1 o2 x = x := fun x => Subtype.ext (hω.one x x.2)
  let 𝒪 : Set (Module.End ℂ Q) := {T | ∃ h hh, T = A h hh}
  let A₀ : Submodule ℂ Q := (augAt om v).comap Q.subtype
  have augle : augAt om v ≤ Q := hN.prop.1.1.trans hN.prop.1.2.1
  have uaug : ∀ z ∈ augAt om v, M.I om (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e : j y = j (y - x) + j x := by rw [← map_add, sub_add_cancel]
      have e2 := I_add' hp hc (jc ⟨y - x, sub_mem hy hx⟩) (jc ⟨x, hx⟩)
      rw [← e, ← hjS _ x hx y hxy, I_left hU hT hp (hc.sch (jc ⟨x, hx⟩))] at e2
      exact (left_eq_add.1 (e2.trans (add_comm _ _)))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero M om
    | add a b ha hb iha ihb => rw [map_add, I_add' hp hc (jc ⟨a, augle ha⟩) (jc ⟨b, augle hb⟩), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  obtain ⟨m1, m2⟩ := max_comap Q (GlobalTheory.Published.ThetaSub om v) (fun P => A₀ ≤ P ∧ ∀ T ∈ 𝒪, ∀ x ∈ P, T x ∈ P)
    (fun _ h => h.2.1) (fun P => ⟨fun h => ⟨fun z hz => ⟨⟨z, augle hz⟩, h.1 hz, rfl⟩, Submodule.map_subtype_le _ _,
      by
        rintro g hg _ ⟨x, hx, rfl⟩ y - hxy
        exact ⟨A g hg x, h.2 _ ⟨g, hg, rfl⟩ x hx, ((hω.acts 1 o1 g hg x x.2 y).1 hxy).symm⟩⟩,
      fun h => ⟨fun x hx => by
          obtain ⟨y, hy, e⟩ := h.1 hx
          rwa [← show y = x from Subtype.ext e], by
        rintro _ ⟨g, hg, rfl⟩ x hx
        obtain ⟨y, hy, e⟩ := h.2.2 g hg x ⟨x, hx, rfl⟩ _ (A g hg x).2 ((hω.acts 1 o1 g hg x x.2 _).2 rfl)
        rwa [← show y = A g hg x from Subtype.ext e]⟩⟩) N hN hu
  have key := absUnit Q β 𝒪 A₀ hs hpos (fun x hx => by rw [hβ, hu', uaug x hx]; simp)
    (by
      rintro _ ⟨h, hh, rfl⟩
      refine ⟨_, ⟨h⁻¹, hinv h hh, rfl⟩, 1, fun x y => ?_⟩
      rw [one_mul, ← iso h hh x, ← Amul h hh h⁻¹ (hinv h hh)]
      simp only [mul_inv_cancel, Aone])
    (fun x₀ => by
      obtain ⟨U, hU1, hUf⟩ := hω.smooth x₀ x₀.2
      obtain ⟨K, hK, hKU, U', hU', hU'K⟩ := hcpt U hU1
      have kk : ∀ k : K, k.1 ∈ UAt σ W (evFin F v) := fun k => (hKU k.2).2
      let κ : K →* Module.End ℂ Q :=
        { toFun := fun k => A k (kk k)
          map_one' := LinearMap.ext Aone
          map_mul' := fun k k' => LinearMap.ext fun x => Amul k (kk k) k' (kk k') x }
      refine ⟨K, inferInstance, κ, fun k => ⟨k, kk k, rfl⟩, fun k => iso k (kk k), fun x => ?_, fun m ρ' hρ => ?_⟩
      · obtain ⟨V, hV1, hVf⟩ := hω.smooth x x.2
        obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover (fun g => (fun y => g⁻¹ * y) ⁻¹' V) fun g _ =>
          (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
            show V ∈ 𝓝 (g⁻¹ * g)
            rwa [inv_mul_cancel])
        refine ⟨t.attach.image fun g => κ ⟨g.1, ht g.1 g.2⟩ x, fun k => Submodule.mem_sup_left (Submodule.subset_span ?_)⟩
        obtain ⟨g, hg, hk⟩ := Set.mem_iUnion₂.1 (hcov k.2)
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨g, hg⟩, Finset.mem_attach _ _, ?_⟩)
        have e : k = ⟨g, ht g hg⟩ * ((⟨g, ht g hg⟩ : K)⁻¹ * k) := by simp
        have e2 : κ ((⟨g, ht g hg⟩ : K)⁻¹ * k) x = x := Subtype.ext (hVf _ hk (kk _))
        conv_rhs => rw [e, map_mul, Module.End.mul_apply, e2]
      · have h1' := hρ fun k => Subtype.ext (hUf k (hKU k.2).1 (kk k))
        obtain ⟨t, ht⟩ := adm U' hU'
        refine ⟨(Finset.univ ×ˢ t).image fun p : Fin m × _ => LinearMap.single ℂ (fun _ => ℂ) p.1 ∘ₗ p.2 ∘ₗ Q.subtype,
          fun L hL hLe => ?_⟩
        have : L = ∑ i, LinearMap.single ℂ (fun _ => ℂ) i ∘ₗ (LinearMap.proj i ∘ₗ L) := by
          ext x i; simp [Pi.single_apply, Finset.sum_apply]
        rw [this]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨l, hl⟩ := LinearMap.exists_extend (LinearMap.proj i ∘ₗ L : Q →ₗ[ℂ] ℂ)
        have hl' : ∀ x : Q, l x = L x i := fun x => LinearMap.congr_fun hl x
        obtain ⟨l', hl't, hll⟩ := ht l (fun z hz => by
            rw [LinearMap.mem_ker, hl' ⟨z, augle hz⟩, show L ⟨z, augle hz⟩ = 0 from hL hz]; rfl)
          fun h hh hh' x hx y hy hxy => by
            have := hLe ⟨h, hU'K ⟨hh, hh'⟩⟩ ⟨x, hx⟩
            rw [h1', Module.End.one_apply] at this
            rw [hl' ⟨x, hx⟩, hl' ⟨y, hy⟩, ← this]
            exact congrFun (congrArg L (Subtype.ext ((hω.acts 1 o1 h hh' x hx y).1 hxy))) i
        have e : (LinearMap.proj i ∘ₗ L : Q →ₗ[ℂ] ℂ) = l' ∘ₗ Q.subtype := LinearMap.ext fun x => (hl' x).symm.trans (hll x x.2)
        rw [e]
        clear e hll
        induction hl't using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, y), by simpa using hy, rfl⟩))
        | zero => simp
        | add a b _ _ ha hb => rw [LinearMap.add_comp, LinearMap.comp_add]; exact add_mem ha hb
        | smul c a _ ha => rw [LinearMap.smul_comp, LinearMap.comp_smul]; exact Submodule.smul_mem _ _ ha)
    _ m1 m2 ⟨φ v, h1 v⟩ hv
  have := L2.eq_zero h𝓕 (uc _) (ui _) (u2 _) ((hβ _ _).symm.trans key)
  rwa [hu', hj, upd_eq] at this

end PositivityTheory.ThKF

end
