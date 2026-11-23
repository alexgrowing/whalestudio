import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ}

theorem conv_of_cpt (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) : ∀ Φ ∈ schA F _, M.Conv o Φ := by
  intro Φ hΦ h
  obtain ⟨t1, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  have hc : Continuous fun g => theta o Φ g h := t1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := c.bdd hc fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h
  exact Measure.integrableOn_of_bounded (M := C) (c.fin _ _ p.good.haar p.good.dom).ne hc.aestronglyMeasurable
    (Eventually.of_forall hC)

theorem I_lin (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (a : ℂ) : M.I o (Φ + a • Ψ) = M.I o Φ + a • M.I o Ψ := by
  funext h
  have e : ∀ g, theta o (Φ + a • Ψ) g h = theta o Φ g h + a * theta o Ψ g h := fun g => by
    simp only [theta, map_add, map_smul]
    rw [thetaSum_add F (p.weil.isUSplitting.pres _ _ hΦ) (Submodule.smul_mem _ _ (p.weil.isUSplitting.pres _ _ hΨ)),
      thetaSum_smul]
  simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (conv_of_cpt hT p c _ hΦ h) ((conv_of_cpt hT p c _ hΨ h).const_mul a), integral_const_mul]

theorem pol_sch (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem int_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (h : IsFundamentalDomain Γ D μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in D, f (x * g) ∂μ = ∫ x in D, f x ∂μ := by
  have h' : IsFundamentalDomain Γ ((fun x => x * g) '' D) μ := by
    simpa [← Set.image_smul] using h.smul_of_comm (MulOpposite.op g)
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (Homeomorph.mulRight g).measurableEmbedding f D]
  exact h'.setIntegral_eq h fun γ x => hf γ γ.2 x

theorem I_act (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g : UA σ Y.J) : M.I o (o (g, 1) Φ) = M.I o Φ := by
  funext h
  obtain ⟨-, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  haveI := c.cnt
  haveI := p.good.haar
  haveI := c.right _ p.good.haar
  have e : ∀ x, theta o (o (g, 1) Φ) x h = theta o Φ (x * g) h := fun x => by
    rw [theta, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact int_right p.good.dom (fun x => theta o Φ x h)
    (fun γ hγ x => by simpa using t2 γ hγ 1 (one_mem _) x h) g

theorem upd_sb {v : Pl F} {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {v : Pl F} {φ φ' : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = φ' u) (z) :
    ∀ᶠ u in cofinite, Function.update φ v z u = φ' u :=
  (h.and (eventually_cofinite_ne v)).mono fun _ e => by rw [Function.update_of_ne e.2]; exact e.1

theorem I_aug (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) (v : Pl F) (f : SInf F (Fin n × Fin d))
    {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    {z₀ z} (h0 : z₀ ∈ SB _) (hz : z ∈ augAt o v) :
    M.I o (pure f (Function.update φ v (z₀ + z))) = M.I o (pure f (Function.update φ v z₀)) := by
  have h3 := (h2.and p.good.std).mono fun _ h => h.1.trans h.2
  obtain ⟨t, ht, ht'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h3
  have mem : ∀ z ∈ SB _, pure f (Function.update φ v z) ∈ schA F _ := fun z hz =>
    GlobalTheory.TensUniq.pure_mem_schA f _ (upd_sb h1 hz) (upd_cof h3 z)
  have add : ∀ z ∈ SB _, ∀ z' ∈ SB _, ∀ a : ℂ, M.I o (pure f (Function.update φ v (z + a • z'))) =
      M.I o (pure f (Function.update φ v z)) + a • M.I o (pure f (Function.update φ v z')) := fun z hz z' hz' a => by
    rw [← I_lin hT p c (mem z hz) (mem z' hz'), ← ht', ← ht', ← ht']
    congr 1
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have zero : M.I o (pure f (Function.update φ v 0)) = 0 := by
    have := add 0 (zero_mem _) 0 (zero_mem _) (-1)
    simpa using this
  have key : z ∈ SB _ ∧ M.I o (pure f (Function.update φ v z)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, -, x, hx, y, hy, a, rfl⟩ := hz
      refine ⟨sub_mem hy hx, ?_⟩
      have e := a t ⟨ht, ht' x ▸ mem x hx⟩
      rw [ht', ht'] at e
      rw [sub_eq_add_neg, ← neg_one_smul ℂ x, add y hy x hx, ← e, I_act hT p c (mem x hx)]
      simp
    | zero => exact ⟨zero_mem _, zero⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by simpa [hx.2, hy.2] using add x hx.1 y hy.1 1⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by simpa [hx.2, zero] using add 0 (zero_mem _) x hx.1 a⟩
  simpa [key.2] using add z₀ h0 z key.1 1

theorem toSo_of (hR : KReal) (hF : KFin) (hK : KCoinv) (hT : ThetaBasic) (hC : CptAll) : ToSo := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hq Φ' hΦ
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Rf, hf⟩ := hF F E σ B a a' G X om om' h
  obtain ⟨-, k1, k2, -⟩ := (hK F E σ B a a' G X om om' R Rf ⟨h, hr, hf⟩).1 _ h.chars.good
  have p := pairV' h
  have c := hC F E σ B _ _ _ _ h.base (.inl p.herm) (by omega)
  have le := pol_sch p.good
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := k2 B.τ₁ (Rf.p' _ (φ B.v₁))
    refine ⟨pure f (Function.update φ B.v₁ y), ⟨Submodule.subset_span ⟨f, hf, _, upd_sb h1 hy.1, upd_cof h2 y, rfl⟩,
      Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 y, by rwa [Function.update_self], rfl⟩⟩, ?_⟩
    have := I_aug hT p c B.v₁ f h1 h2 hy.1 ((k1 _ (sub_mem (h1 _) hy.1)).1 (by rw [map_sub, e, sub_self]))
    rw [← this, add_sub_cancel, Function.update_eq_self]
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y hx hy ix iy =>
    obtain ⟨x', mx, ex⟩ := ix
    obtain ⟨y', my, ey⟩ := iy
    refine ⟨x' + y', add_mem mx my, ?_⟩
    rw [← one_smul ℂ y, ← one_smul ℂ y', I_lin hT p c (le mx.1) (le my.1), I_lin hT p c (le hx) (le hy), ex, ey]
  | smul t x hx ix =>
    obtain ⟨x', mx, ex⟩ := ix
    refine ⟨t • x', Submodule.smul_mem _ _ mx, ?_⟩
    rw [← zero_add (t • x), ← zero_add (t • x'), I_lin hT p c (zero_mem _) (le mx.1), I_lin hT p c (zero_mem _) (le hx), ex]

end GlobalTheory.ThK.Dbl

end
