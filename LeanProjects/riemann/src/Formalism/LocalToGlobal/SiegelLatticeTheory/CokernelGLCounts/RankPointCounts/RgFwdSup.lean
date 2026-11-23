import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG5

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem rg_fwd_sup_lemma {g₁ g₂ : Fin (r + 1) → V} {U₁ U₂ W₁ W₂ : Submodule E V}
    (ψ : W₁ ≃ₗ[E] W₂) (hW₁ : W₁ ≤ H.perp (H.X g₁)) (hW₂ : W₂ ≤ H.perp (H.X g₂))
    (hX : H.X g₂ ≤ U₂) (hd : Disjoint U₂ W₂) (φ : H.Wb g₁ ≃ₗ[E] H.Wb g₂)
    (hC1 : ∀ w : W₁, φ (H.mkW g₁ ⟨w, hW₁ w.2⟩) = H.mkW g₂ ⟨ψ w, hW₂ (ψ w).2⟩)
    (hC2 : ∀ u ∈ U₁, ∀ hu : u ∈ H.perp (H.X g₁), ∃ u' ∈ U₂, ∃ hu' : u' ∈ H.perp (H.X g₂),
      φ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩)
    {a u : V} (ha : a ∈ U₁) (ha' : a ∈ H.perp (H.X g₁)) (b w : W₁) (hu : u ∈ U₂)
    (hu' : u ∈ H.perp (H.X g₂)) (hy : a + b ∈ H.perp (H.X g₁)) (hx : u + ψ w ∈ H.perp (H.X g₂))
    (h : φ (H.mkW g₁ ⟨a + b, hy⟩) = H.mkW g₂ ⟨u + ψ w, hx⟩) :
    b = w ∧ φ (H.mkW g₁ ⟨a, ha'⟩) = H.mkW g₂ ⟨u, hu'⟩ := by
  obtain ⟨a₂, ha₂, ha₂', e⟩ := hC2 a ha ha'
  rw [mkW_add H a b ha' (hW₁ b.2), map_add, e, hC1, mkW_add H u _ hu' (hW₂ (ψ w).2)] at h
  have h5 : H.mkW g₂ (⟨a₂, ha₂'⟩ + ⟨ψ b, hW₂ (ψ b).2⟩) =
      H.mkW g₂ (⟨u, hu'⟩ + ⟨ψ w, hW₂ (ψ w).2⟩) := by
    rw [map_add, map_add]
    exact h
  simp only [HermSp.mkW, Submodule.mkQ_apply] at h5
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h5
  simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_add] at h5
  have h6 : ((ψ (b - w) : W₂) : V) ∈ U₂ := by
    have e2 : ((ψ (b - w) : W₂) : V) = (a₂ + ↑(ψ b) - (u + ↑(ψ w))) - (a₂ - u) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [e2]
    exact U₂.sub_mem (hX h5) (U₂.sub_mem ha₂ hu)
  have h0 : ((ψ (b - w) : W₂) : V) = 0 := (Submodule.disjoint_def.1 hd) _ h6 (ψ (b - w)).2
  have h7 : ψ (b - w) = 0 := Subtype.ext (by rw [h0]; rfl)
  have hbw : b = w := sub_eq_zero.1 (ψ.map_eq_zero_iff.1 h7)
  subst hbw
  refine ⟨rfl, ?_⟩
  rw [e]
  exact add_right_cancel h

private theorem mem_span_frames_of_mmSharp (t : Term V M r) (m : MMsharp H t) :
    (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have h : (m : V) ∈ Submodule.span E (Set.range (H.MMfam t)) := m.2.1
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨i, rfl⟩
  have hf : ∀ j, t.f j ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
    fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hf' : ∀ j, t.f' j ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  unfold HermSp.MMfam
  generalize M.split = s
  rcases s with _ | g <;> rcases i with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr]
  all_goals first
    | exact hf j
    | exact hf' j
    | exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' j) (hf j))

theorem rg_fwd_sup (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hI : Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩) :
    GamR H t₂ (algebraMap F E (g.q : F)) ⊆
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) := by
  intro p hp
  obtain ⟨u, u', u'', hu, hu', huu, rfl⟩ := hp
  have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  have hU : ∀ (t : Term V M r) (m : MMsharp H t),
      (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := mem_span_frames_of_mmSharp H
  have hXf : ∀ t : Term V M r, H.X t.f ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
    fun t => Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl _, rfl⟩)
  have hXf' : ∀ t : Term V M r, H.X t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
    fun t => Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr _, rfl⟩)
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ u))
  obtain ⟨m'', hm''⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ u''))
  obtain ⟨w, -, hw⟩ := (D.hθ m u).1 (by
    rw [show ddMk H t₁ m = θ.symm (ddMk H t₂ u) from hm]
    exact θ.apply_symm_apply _)
  obtain ⟨w'', -, hw''⟩ := (D.hθ m'' u'').1 (by
    rw [show ddMk H t₁ m'' = θ.symm (ddMk H t₂ u'') from hm'']
    exact θ.apply_symm_apply _)
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  have hw' : (u' : V) + ↑(ψ (w - c • w'')) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ (w - c • w'')) = ((u : V) + ↑(ψ w)) - c • ((u'' : V) + ↑(ψ w'')) := by
      rw [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hw (hcx _ hw'')
  have hx₂ : (u : V) + ↑(ψ w) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2)
  have hx₂' : (u' : V) + ↑(ψ (w - c • w'')) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hdiff₂ : ((u : V) + ↑(ψ w)) - ((u' : V) + ↑(ψ (w - c • w''))) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ w)) - ((u' : V) + ↑(ψ (w - c • w''))) = c • ((u'' : V) + ↑(ψ w'')) := by
      rw [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hw'', rfl⟩
  have hmem : (H.mkW t₂.f' ⟨_, hx₂'⟩, H.mkW t₂.f ⟨_, hx₂⟩) ∈
      H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ :=
    ⟨⟨_, hx₂'⟩, ⟨_, hx₂⟩, hw', hw, hdiff₂, rfl⟩
  rw [← hI] at hmem
  obtain ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, hye⟩ := hmem
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  simp only [Prod.map, Prod.mk.injEq] at hye
  obtain ⟨hφ', hφ⟩ := hye
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  obtain ⟨hbw, hφa⟩ := rg_fwd_sup_lemma H ψ (fun x hx => mem_perp_isotropicSpan_of_mem_framePerp H hx)
    (fun x hx => mem_perp_isotropicSpan_of_mem_framePerp H hx) (hXf t₂) D.hU₂.disjoint φ D.hC1 D.hC2 ha hap ⟨b, hb⟩ w
    (hU t₂ u) hu (by rw [hab]; exact x₁.2) hx₂
    (by rw [← hφ]; exact congrArg φ (mkW_congr H _ x₁.2 hab))
  obtain ⟨hbw', hφa'⟩ := rg_fwd_sup_lemma H ψ (fun x hx => mem_perp_isotropicSpan_of_mem_framePerp' H hx)
    (fun x hx => mem_perp_isotropicSpan_of_mem_framePerp' H hx) (hXf' t₂) D.hU₂.disjoint φ' D.hC1' D.hC2' ha' hap' ⟨b', hb'⟩
    (w - c • w'') (hU t₂ u') hu' (by rw [hab']; exact x₁'.2) hx₂'
    (by rw [← hφ']; exact congrArg φ' (mkW_congr H _ x₁'.2 hab'))
  have hb''w : b'' = ↑w'' := by
    have e1 : b = ↑w := by rw [← hbw]
    have e2 : b' = ↑w - c • ↑w'' := by
      rw [← Submodule.coe_smul, ← Submodule.coe_sub, ← hbw']
    have e3 : c • (b'' - ↑w'') = 0 := by
      rw [smul_sub, ← hdb, e1, e2]
      abel
    have e4 : b'' - ↑w'' = 0 := by
      calc b'' - ↑w'' = algebraMap F E (g.q : F)⁻¹ • (c • (b'' - ↑w'')) := by
            rw [smul_smul, hc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_smul]
        _ = 0 := by rw [e3, smul_zero]
    exact sub_eq_zero.1 e4
  have hθ1 : θ (ddMk H t₁ ⟨a, haS⟩) = ddMk H t₂ u :=
    (D.hθ _ _).2 ⟨⟨b, hb⟩, by
      show a + b ∈ t₁.abelian₂
      rw [hab]
      exact hx₁L, by
      rw [hbw]
      exact hw⟩
  have hθ2 : θ (ddMk H t₁ ⟨a'', haS''⟩) = ddMk H t₂ u'' :=
    (D.hθ _ _).2 ⟨⟨b'', hb''⟩, by
      show a'' + b'' ∈ t₁.abelian₂
      rw [hab'']
      exact hl, by
      rw [show (⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') = w'' from Subtype.ext hb''w]
      exact hw''⟩
  refine ⟨(ddMk H t₁ ⟨a, haS⟩, ddMk H t₁ ⟨a'', haS''⟩, H.mkW t₁.f ⟨a, hap⟩, H.mkW t₁.f' ⟨a', hap'⟩),
    ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, ?_⟩
  show (θ _, θ _, φ _, φ' _) = _
  rw [hθ1, hθ2, hφa, hφa']

end RG5

end Formalism.L2.SG.LsDatumA
