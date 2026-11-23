import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd

noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open MeasureTheory PositivityTheory.ThKEnd.Two

theorem isAv_transport {A B H : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [Mul H] {Γ : Subgroup A} {Δ : Subgroup B}
    (e : A ≃ₜ* B) (he : ∀ x, e x ∈ Δ ↔ x ∈ Γ) {ι : B → H} {f c : H → ℂ} (h : IsAv Δ ι f c) : IsAv Γ (fun x => ι (e x)) f c := by
  intro μ 𝓕 h1 h2 h3 x
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have mp : MeasurePreserving e.symm (μ.map e) μ := (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv ⟨hm.measurable, rfl⟩ :)
  let k : Γ ≃ Δ := e.toEquiv.subtypeEquiv fun a => (he a).symm
  have h4 : IsFundamentalDomain Δ (e.symm ⁻¹' 𝓕) (μ.map e) :=
    h2.preimage_of_equiv mp.quasiMeasurePreserving k.bijective fun γ y => by
      change e.symm (e γ * y) = γ * e.symm y
      simp
  have h5 : e ⁻¹' (e.symm ⁻¹' 𝓕) = 𝓕 := by ext y; simp
  rw [h (μ.map e) _ inferInstance h4 (by rw [hm.map_apply, h5, h3]), hm.setIntegral_map, h5]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] {Γ S A : Subgroup G} {f c : G → ℂ}

theorem zero_of_retract (hS : IsClosed (S : Set G)) (hA : IsClosed (A : Set G)) (le : A ≤ S) (L : Lat (Γ.subgroupOf S))
    (LA : Lat (Γ.subgroupOf A)) (ρ : S →* S) (hρ : Continuous ρ) (ρρ : ∀ s, ρ (ρ s) = ρ s) (ker : ∀ s, s.1 ∈ A ↔ ρ s = 1)
    (rat : ∀ s, s.1 ∈ Γ → (ρ s).1 ∈ Γ) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (h0 : IsAv (Γ.subgroupOf A) (fun a => a.1) f 0) : IsAv (Γ.subgroupOf S) (fun a => a.1) f 0 := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology A := TopologicalSpace.Subtype.secondCountableTopology _
  let B : Subgroup S := ρ.eqLocus (MonoidHom.id S)
  have hB : IsClosed (B : Set S) := isClosed_eq hρ continuous_id
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  let π : S →* B := ρ.codRestrict B ρρ
  have cπ : Continuous π := hρ.subtype_mk _
  have sm : Semi (Γ.subgroupOf S) (Γ.subgroupOf A) ((Γ.subgroupOf S).subgroupOf B) (Subgroup.inclusion le) B.subtype
      (fun s => ⟨(s * (ρ s)⁻¹).1, (ker _).2 (by simp [ρρ])⟩) π :=
    ⟨continuous_subtype_val.subtype_mk _, continuous_subtype_val,
      (continuous_subtype_val.comp (continuous_id.mul hρ.inv)).subtype_mk _, cπ, Subgroup.inclusion_injective le,
      fun s => Subtype.ext (inv_mul_cancel_right s.1 (ρ s).1), fun a => Subtype.ext ((ker _).1 a.2), fun b => Subtype.ext b.2, fun _ => Iff.rfl,
      fun _ h => h, fun s h => rat s h⟩
  have := L.cnt
  have := L.disc
  let i : ((Γ.subgroupOf S).subgroupOf B) → Γ.subgroupOf S := fun x => ⟨x.1.1, x.2⟩
  have ii : Function.Injective i := fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  have LB : Lat ((Γ.subgroupOf S).subgroupOf B) := by
    obtain ⟨C, c1, c2⟩ := L.cov
    refine ⟨ii.countable, DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ii, _, c1.image cπ, fun b => ?_⟩
    obtain ⟨γ, g1, g2⟩ := c2 b.1
    exact ⟨π γ, rat γ g1, _, g2, by rw [map_mul, show π b.1 = b from Subtype.ext b.2]⟩
  exact sm.stage L LA LB (inc := S.subtype) continuous_subtype_val hc (fun γ h => hf _ h) h0 fun _ _ _ _ _ _ => by simp

variable {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

def prodG (A : Subgroup G) (ι : B →* G) (hn : ∀ b, ∀ a ∈ A, ι b * a * (ι b)⁻¹ ∈ A) : Subgroup G where
  carrier := {s | ∃ b, s * (ι b)⁻¹ ∈ A}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro s t ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b * b', by simpa [mul_assoc] using mul_mem hb (hn b _ hb')⟩
  inv_mem' := by
    rintro s ⟨b, hb⟩
    exact ⟨b⁻¹, by simpa [mul_assoc] using hn b⁻¹ _ (inv_mem hb)⟩

variable [MeasurableSpace B] [BorelSpace B] [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] {Δ : Subgroup B}

theorem prod_stage [Countable Γ] [DiscreteTopology Γ] (hA : IsClosed (A : Set G)) (LA : Lat (Γ.subgroupOf A)) (LB : Lat Δ) {ι : B →* G}
    (hι : Continuous ι) (hn : ∀ b, ∀ a ∈ A, ι b * a * (ι b)⁻¹ ∈ A) (π : G → B) (hπ : Continuous π) (hπι : ∀ a ∈ A, ∀ b, π (a * ι b) = b)
    (r1 : ∀ b ∈ Δ, ι b ∈ Γ) (r2 : ∀ γ ∈ Γ, π γ ∈ Δ) : IsClosed (prodG A ι hn : Set G) ∧ Lat (Γ.subgroupOf (prodG A ι hn)) ∧
      ∀ f cA c : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → IsAv (Γ.subgroupOf A) (fun a => a.1) f cA →
        IsAv Δ ι cA c → IsAv (Γ.subgroupOf (prodG A ι hn)) (fun a => a.1) f c := by
  have k : ∀ s b, s * (ι b)⁻¹ ∈ A → π s = b := fun s b h => by simpa using hπι _ h b
  have k' : ∀ s : prodG A ι hn, s.1 * (ι (π s))⁻¹ ∈ A := fun ⟨s, b, h⟩ => by rwa [k s b h]
  have hS : IsClosed (prodG A ι hn : Set G) := by
    have : (prodG A ι hn : Set G) = (fun s => s * (ι (π s))⁻¹) ⁻¹' A := Set.ext fun s => ⟨fun h => k' ⟨s, h⟩, fun h => ⟨_, h⟩⟩
    rw [this]
    exact hA.preimage (by fun_prop)
  haveI : LocallyCompactSpace (prodG A ι hn) := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (prodG A ι hn) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology A := TopologicalSpace.Subtype.secondCountableTopology _
  have le : A ≤ prodG A ι hn := fun a h => ⟨1, by simpa using h⟩
  let π' : prodG A ι hn →* B := MonoidHom.mk' (fun s => π s) fun s t => k _ _ (by
    simpa [mul_assoc] using mul_mem (k' s) (hn (π s) _ (k' t)))
  have sm : Semi (Γ.subgroupOf (prodG A ι hn)) (Γ.subgroupOf A) Δ (Subgroup.inclusion le)
      (ι.codRestrict _ fun b => ⟨b, by simp⟩) (fun s => ⟨_, k' s⟩) π' :=
    ⟨continuous_subtype_val.subtype_mk _, hι.subtype_mk _, Continuous.subtype_mk (by fun_prop) _,
      hπ.comp continuous_subtype_val, Subgroup.inclusion_injective le, fun s => Subtype.ext (inv_mul_cancel_right s.1 _),
      fun a => k _ _ (by simp), fun b => k (ι b) b (by simp), fun _ => Iff.rfl, fun b h => r1 b h, fun s h => r2 s h⟩
  let i : Γ.subgroupOf (prodG A ι hn) → Γ := fun x => ⟨x.1.1, x.2⟩
  have ii : Function.Injective i := fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  have L := sm.lat LA LB ii.countable (DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ii)
  exact ⟨hS, L, fun f cA c hc hf h1 h2 => sm.stage L LA LB (inc := Subgroup.subtype _) continuous_subtype_val hc
    (fun γ h => hf _ h) h1 h2⟩

end PositivityTheory.ThKEnd.Cusp

end
