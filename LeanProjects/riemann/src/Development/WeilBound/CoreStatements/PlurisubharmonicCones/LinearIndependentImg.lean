import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange

noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

variable {E L Ψ V : Type} [Field E] [NumberField E] [Field L] [NumberField L] [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

open TorPart in
theorem tor_facts [Fintype Ψ] (hΨ : 2 * Fintype.card Ψ = Module.finrank ℚ E) {r : ℕ} {v : Fin r → V}
    (hv : IsOFamily A.ρ A.I v) (s : Ψ ⊕ Ψ) :
    LinearIndependent L (fun a => eigComp A.ρ (A.σ s) (v a)) ∧
      (∀ a, eigComp A.ρ (A.σ s) (v a) ∈ eigSp A.ρ (A.σ s)) ∧
      (∀ a, eigComp A.ρ (A.σ s) (v a) ∈ Submodule.span L (A.I : Set V)) ∧
      ∀ x ∈ A.tor s, x ∈ Submodule.span L (Set.range fun a => eigComp A.ρ (A.σ s) (v a)) := by
  classical
  have hres : Function.Bijective (fun t : E →+* L => t.comp (algebraMap (𝓞 E) E)) := by
    refine ⟨fun a b h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h, fun g => ?_⟩
    obtain ⟨q, rfl⟩ := A.σ_bij.2 g
    exact ⟨IsFractionRing.lift (A.σ_inj q), RingHom.ext fun x => IsFractionRing.lift_algebraMap (A.σ_inj q) x⟩
  have hfin1 : Finite (𝓞 E →+* L) := Finite.of_surjective A.σ A.σ_bij.2
  have hfin2 : Finite (E →+* L) := Finite.of_injective _ hres.1
  letI : Fintype (E →+* L) := Fintype.ofFinite _
  have hcard : Fintype.card (E →+* L) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.ofBijective _ hres),
      ← Nat.card_congr (Equiv.ofBijective _ A.σ_bij), ← hΨ, Nat.card_eq_fintype_card,
      Fintype.card_sum]
    ring
  obtain ⟨t, ht⟩ := hres.2 (A.σ s)
  change t.comp (algebraMap (𝓞 E) E) = A.σ s at ht
  have hsur : ∀ σ' : 𝓞 E →+* L, ∃ u : E →+* L, u.comp (algebraMap (𝓞 E) E) = σ' := hres.2
  have hc : ∀ a, eigComp A.ρ (A.σ s) (v a) = HT.eigProj A.ρ t (v a) := fun a => by
    rw [← ht, eigComp_comp hcard hsur]
  have htor : A.tor s = Submodule.span (𝓞 L) (A.I : Set V) ⊓ (HT.eigSp A.ρ t).restrictScalars (𝓞 L) := by
    rw [LinPt.tor, ← ht, eigSp_comp]
  simp only [hc]
  refine ⟨?_, fun a => ?_, fun a => ?_, fun x hx => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h := phi_injective hcard A.ρ hv A.I_stable A.I_basis t (a₁ := g) (a₂ := 0)
      (by rw [phi_apply, hg, map_zero])
    rw [h]
    rfl
  · rw [← ht, eigSp_comp]
    exact HT.LatBasic.eigProj_mem A.ρ t _
  · simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (A.I_stable _ _ (hv.1 a)))
  · rw [htor, ← map_eigenLat hcard A.ρ hv A.I_stable A.I_basis t] at hx
    obtain ⟨w, -, rfl⟩ := hx
    rw [phi_apply]
    exact sum_mem fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem span_I_le : Submodule.span (𝓞 L) (A.I : Set V) ≤ A.Λ := Submodule.span_le.2 fun x hx => A.I_le x hx

theorem mem_span_I {x : V} (hx : x ∈ A.Λ) (h : x ∈ Submodule.span L (A.I : Set V)) :
    x ∈ Submodule.span (𝓞 L) (A.I : Set V) := by
  obtain ⟨c, hc, h1⟩ := exists_smul_mem_of_mem_span (Submodule.span (𝓞 L) (A.I : Set V))
    (fun y hy => Submodule.subset_span hy) h
  have h2 := (A.ker (c • ⟨x, hx⟩)).2 h1
  rw [map_smul] at h2
  exact (A.ker ⟨x, hx⟩).1 ((smul_eq_zero.1 h2).resolve_left hc)

theorem tor_le_eig (s : Ψ ⊕ Ψ) : A.tor s ≤ A.eig s := inf_le_inf_right _ (span_I_le A)

theorem range_append {α : Type} {r k : ℕ} (w : Fin r → α) (q : Fin k → α) :
    Set.range (Fin.append w q) = Set.range w ∪ Set.range q := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun a => ?_) (fun c => ?_) i
    · exact Or.inl ⟨a, (Fin.append_left _ _ _).symm⟩
    · exact Or.inr ⟨c, (Fin.append_right _ _ _).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, Fin.append_left _ _ a⟩
    · exact ⟨_, Fin.append_right _ _ c⟩

theorem coeff_eq_zero {r k : ℕ} {w : Fin r → V} {q : Fin k → V} (h : LinearIndependent L (Fin.append w q))
    (c : Fin k → 𝓞 L) (hc : ∑ j, c j • q j ∈ Submodule.span L (Set.range w)) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hc
  have h1 := Fintype.linearIndependent_iff.1 h (Fin.append (fun a => -d a) fun j => algebraMap (𝓞 L) L (c j)) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib, algebraMap_smul, hd]
    exact neg_add_cancel _)
  funext j
  have h2 := h1 (Fin.natAdd r j)
  rw [Fin.append_right, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)] at h2
  exact h2

variable {s : Ψ ⊕ Ψ} {r k : ℕ} {w : Fin r → V} {q : Fin k → A.Λ}

theorem linearIndependent_img (hb : LinearIndependent L (Fin.append w fun c => (q c : V)))
    (h4 : ∀ x ∈ A.tor s, x ∈ Submodule.span L (Set.range w)) (hq : ∀ c, (q c : V) ∈ A.eig s) :
    LinearIndependent (𝓞 L) fun c => A.f (q c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : A.f (∑ c, g c • q c) = 0 := by simpa only [map_sum, map_smul] using hg
  have h2 := (A.ker _).1 h1
  have e : ((∑ c, g c • q c : A.Λ) : V) = ∑ c, g c • (q c : V) := by simp
  rw [e] at h2
  have h3 : ∑ c, g c • (q c : V) ∈ A.eig s := sum_mem fun c _ => (A.eig s).smul_mem _ (hq c)
  exact congrFun (coeff_eq_zero hb g (h4 _ ⟨h2, h3.2⟩)) j

theorem index_abstract {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {B₁ B₂ M T : Submodule R N}
    (hTM : T ≤ M) (hB₂M : B₂ ≤ M) (hB₁T : ∀ x ∈ B₁, x ∈ M → x ∈ T) (k1 : (B₁ ⊔ B₂) ⊓ T = B₁ ⊓ T) :
    (B₁ ⊔ B₂).toAddSubgroup.relIndex M.toAddSubgroup =
      B₁.toAddSubgroup.relIndex T.toAddSubgroup * (T ⊔ B₂).toAddSubgroup.relIndex M.toAddSubgroup ∧
    M.toAddSubgroup.relIndex (B₁ ⊔ B₂).toAddSubgroup = T.toAddSubgroup.relIndex B₁.toAddSubgroup := by
  have k2 : T ⊔ (B₁ ⊔ B₂) ⊓ M = T ⊔ B₂ := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (le_inf le_sup_right hB₂M) _)
    rintro x ⟨hx, hxM⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h5 := M.sub_mem hxM (hB₂M hz)
    rw [add_sub_cancel_right] at h5
    exact Submodule.add_mem_sup (hB₁T y hy h5) hz
  have k3 : B₁ ⊔ M ⊓ (B₁ ⊔ B₂) = B₁ ⊔ B₂ :=
    le_antisymm (sup_le le_sup_left inf_le_right) (sup_le_sup_left (le_inf hB₂M le_sup_right) _)
  have k4 : M ⊓ (B₁ ⊔ B₂) ⊓ B₁ = T ⊓ B₁ :=
    le_antisymm (fun x hx => ⟨hB₁T x hx.2 hx.1.1, hx.2⟩) fun x hx => ⟨⟨hTM hx.1, Submodule.mem_sup_left hx.2⟩, hx.2⟩
  have inf_r : ∀ X Y : Submodule R N, (X ⊓ Y).toAddSubgroup.relIndex Y.toAddSubgroup =
      X.toAddSubgroup.relIndex Y.toAddSubgroup := fun X Y => by
    have h : (X ⊓ Y).toAddSubgroup = X.toAddSubgroup ⊓ Y.toAddSubgroup := AddSubgroup.ext fun _ => Iff.rfl
    rw [h, AddSubgroup.inf_relIndex_right]
  have sup_r : ∀ X Y : Submodule R N, Y.toAddSubgroup.relIndex (X ⊔ Y).toAddSubgroup =
      Y.toAddSubgroup.relIndex X.toAddSubgroup := fun X Y => by
    rw [Submodule.sup_toAddSubgroup]
    exact AddSubgroup.relIndex_sup_right _ _
  constructor
  · have e1 := AddSubgroup.relIndex_mul_relIndex ((B₁ ⊔ B₂) ⊓ M).toAddSubgroup (T ⊔ (B₁ ⊔ B₂) ⊓ M).toAddSubgroup
      M.toAddSubgroup (fun x hx => Submodule.mem_sup_right hx)
      fun x hx => (sup_le hTM inf_le_right : T ⊔ (B₁ ⊔ B₂) ⊓ M ≤ M) hx
    have e2 : ((B₁ ⊔ B₂) ⊓ M).toAddSubgroup.relIndex T.toAddSubgroup = B₁.toAddSubgroup.relIndex T.toAddSubgroup := by
      rw [← inf_r _ T, inf_assoc, inf_eq_right.2 hTM, k1, inf_r]
    rw [← inf_r (B₁ ⊔ B₂) M, ← e1, sup_r, e2, k2]
  · have e1 := sup_r B₁ (M ⊓ (B₁ ⊔ B₂))
    rw [k3, inf_r] at e1
    rw [e1, ← inf_r _ B₁, k4, inf_r]

theorem index_quot {R N N' : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    {Λ M T : Submodule R N} (f : Λ →ₗ[R] N') (hM : M ≤ Λ) {k : ℕ} (q : Fin k → Λ) (hq : ∀ c, (q c : N) ∈ M)
    (hT : ∀ x : Λ, (x : N) ∈ M → (f x = 0 ↔ (x : N) ∈ T)) :
    (T ⊔ Submodule.span R (Set.range fun c => (q c : N))).toAddSubgroup.relIndex M.toAddSubgroup =
      (Submodule.span R (Set.range fun c => f (q c))).toAddSubgroup.relIndex
        ((M.comap Λ.subtype).map f).toAddSubgroup := by
  have e3 := AddSubgroup.relIndex_comap (T ⊔ Submodule.span R (Set.range fun c => (q c : N))).toAddSubgroup
    Λ.subtype.toAddMonoidHom (M.comap Λ.subtype).toAddSubgroup
  have e4 : (M.comap Λ.subtype).toAddSubgroup.map Λ.subtype.toAddMonoidHom = M.toAddSubgroup := by
    have : (M.comap Λ.subtype).map Λ.subtype = M := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hM
    exact congrArg Submodule.toAddSubgroup this
  have e5 := AddSubgroup.relIndex_comap (Submodule.span R (Set.range fun c => f (q c))).toAddSubgroup
    f.toAddMonoidHom (M.comap Λ.subtype).toAddSubgroup
  rw [e4] at e3
  refine e3.symm.trans (Eq.trans ?_ e5)
  rw [← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap f.toAddMonoidHom _)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  refine and_congr_left fun hxM => ?_
  have hxM' : (x : N) ∈ M := hxM
  have key : ∀ c : Fin k → R, f x = ∑ j, c j • f (q j) ↔ (x : N) - ∑ j, c j • (q j : N) ∈ T := fun c => by
    have e : ((x - ∑ j, c j • q j : Λ) : N) = x - ∑ j, c j • (q j : N) := by simp
    have h1 := hT (x - ∑ j, c j • q j) (by
      rw [e]
      exact M.sub_mem hxM' (sum_mem fun j _ => M.smul_mem _ (hq j)))
    rw [e, map_sub, sub_eq_zero] at h1
    simpa only [map_sum, map_smul] using h1
  change (x : N) ∈ T ⊔ Submodule.span R (Set.range fun c => (q c : N)) ↔ f x ∈ _
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hz
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, ((key c).2 ?_).symm⟩
    rw [← hyz, add_sub_cancel_right]
    exact hy
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
    exact Submodule.mem_sup.2 ⟨_, (key c).1 hc.symm, _, (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, rfl⟩,
      sub_add_cancel _ _⟩

theorem index_split (hb : LinearIndependent L (Fin.append w fun c => (q c : V)))
    (h3 : ∀ a, w a ∈ Submodule.span L (A.I : Set V))
    (h4 : ∀ x ∈ A.tor s, x ∈ Submodule.span L (Set.range w)) (hq : ∀ c, (q c : V) ∈ A.eig s) :
    (Submodule.span (𝓞 L) (Set.range (Fin.append w fun c => (q c : V)))).toAddSubgroup.relIndex
        (A.eig s).toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range w)).toAddSubgroup.relIndex (A.tor s).toAddSubgroup *
        (Submodule.span (𝓞 L) (Set.range fun c => A.f (q c))).toAddSubgroup.relIndex (A.img s).toAddSubgroup ∧
    (A.eig s).toAddSubgroup.relIndex
        (Submodule.span (𝓞 L) (Set.range (Fin.append w fun c => (q c : V)))).toAddSubgroup =
      (A.tor s).toAddSubgroup.relIndex (Submodule.span (𝓞 L) (Set.range w)).toAddSubgroup := by
  have hB₁L : ∀ x ∈ Submodule.span (𝓞 L) (Set.range w), x ∈ Submodule.span L (Set.range w) := fun x hx =>
    Submodule.span_le_restrictScalars (𝓞 L) L _ hx
  have hwI : Submodule.span L (Set.range w) ≤ Submodule.span L (A.I : Set V) :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h3 a)
  have hB₂ : Submodule.span (𝓞 L) (Set.range fun c => (q c : V)) ≤ A.eig s :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hq c)
  have k1 : (Submodule.span (𝓞 L) (Set.range w) ⊔ Submodule.span (𝓞 L) (Set.range fun c => (q c : V))) ⊓ A.tor s =
      Submodule.span (𝓞 L) (Set.range w) ⊓ A.tor s := by
    refine le_antisymm ?_ (inf_le_inf_right _ le_sup_left)
    intro x hx'
    obtain ⟨hx, hxT⟩ := Submodule.mem_inf.1 hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 hz
    have h5 := Submodule.sub_mem _ (h4 _ hxT) (hB₁L y hy)
    rw [add_sub_cancel_left] at h5
    have h6 := coeff_eq_zero hb c h5
    refine Submodule.mem_inf.2 ⟨?_, hxT⟩
    rw [h6]
    simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] using hy
  have h := index_abstract (tor_le_eig A s) hB₂ (fun x hx hxM => Submodule.mem_inf.2
    ⟨mem_span_I A (Submodule.mem_inf.1 hxM).1 (hwI (hB₁L x hx)), (Submodule.mem_inf.1 hxM).2⟩) k1
  have h' := index_quot (M := A.eig s) (T := A.tor s) A.f inf_le_left q hq fun x hx =>
    (A.ker x).trans ⟨fun h => Submodule.mem_inf.2 ⟨h, (Submodule.mem_inf.1 hx).2⟩, fun h => (Submodule.mem_inf.1 h).1⟩
  rw [h'] at h
  rw [range_append, Submodule.span_union]
  exact h

theorem gramDet_eq (ι : L →+* ℂ) (q : Fin k → A.Λ) :
    A.gramDet ι q = GroundTheory.Heights₂.Heights.gramDet A.Bq.metric ι fun c => A.f (q c) := rfl

theorem rank_img (hli : LinearIndependent (𝓞 L) fun c => A.f (q c)) (hq : ∀ c, (q c : V) ∈ A.eig s)
    (hi : (Submodule.span (𝓞 L) (Set.range fun c => A.f (q c))).toAddSubgroup.relIndex (A.img s).toAddSubgroup ≠ 0) :
    A.Bq.rank (A.img s) = k ∧ A.Bq.degree (A.img s) =
      Real.log ((Submodule.span (𝓞 L) (Set.range fun c => A.f (q c))).toAddSubgroup.relIndex
        (A.img s).toAddSubgroup : ℕ) - (∑ ι : L →+* ℂ, Real.log (A.gramDet ι q)) / 2 := by
  let y : Fin k → A.img s := fun c => ⟨A.f (q c), q c, hq c, rfl⟩
  have hy : LinearIndependent (𝓞 L) y := LinearIndependent.of_comp (A.img s).subtype hli
  have hsp : (Submodule.span (𝓞 L) (Set.range fun c => A.f (q c))).comap (A.img s).subtype =
      Submodule.span (𝓞 L) (Set.range y) := by
    rw [← Submodule.comap_map_eq_of_injective (A.img s).injective_subtype (Submodule.span (𝓞 L) (Set.range y)),
      Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 L) (Set.range fun c => A.f (q c))).toAddSubgroup.relIndex (A.img s).toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup.index := by
    rw [← hsp]
    rfl
  rw [hidx] at hi ⊢
  have hr : Module.finrank (𝓞 L) (A.img s) = k := by
    rw [← LatticeLemmas.finrank_submodule_eq (Submodule.span (𝓞 L) (Set.range y)) fun x => ?_,
      finrank_span_eq_card hy, Fintype.card_fin]
    refine ⟨((Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup.index : 𝓞 L), Nat.cast_ne_zero.2 hi, ?_⟩
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_index_mem (Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup x
  refine ⟨hr, ?_⟩
  rw [HermitianBundle.degree_eq_arithDegree, arithDegree_eq _ hy (by rw [Fintype.card_fin, hr]), degreeWith,
    one_div_mul_eq_div]
  rfl

end LevelTowerAlt
