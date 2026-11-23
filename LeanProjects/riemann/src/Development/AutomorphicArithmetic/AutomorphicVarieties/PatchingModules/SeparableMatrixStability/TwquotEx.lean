import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.QuotEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomlDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_desc {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (g : G.Hom G')
    (H : OpenNormalSubgroup G.Γ) (hk : g.p.ker ≤ H.toSubgroup) :
    ∃ H' : OpenNormalSubgroup G'.Γ, H'.toSubgroup.comap g.p = H.toSubgroup := by
  have e : (H.toSubgroup.map g.p).comap g.p = H.toSubgroup := Subgroup.comap_map_eq_self hk
  have hq : Topology.IsQuotientMap g.p := g.cont.isClosedMap.isQuotientMap g.cont g.surj
  have ho : IsOpen (H.toSubgroup.map g.p : Set G'.Γ) := by
    rw [← hq.isOpen_preimage, ← Subgroup.coe_comap, e]
    exact H.toOpenSubgroup.isOpen
  exact ⟨{ toSubgroup := H.toSubgroup.map g.p, isOpen' := ho, isNormal' := H.isNormal'.map _ g.surj }, e⟩

theorem UpperTheory.V.Pa.twquot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), Nonempty (TWQuot T) := by
  intro l _ L G0 T
  haveI hn : T.H.toSubgroup.Normal := T.H.isNormal'
  have ho : IsOpen (T.H.toSubgroup : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hoN : ∀ N, IsOpen (T.H.toSubgroup.comap (T.h N).p : Set (T.GN N).Γ) := fun N => ho.preimage (T.h N).cont
  obtain ⟨G0', g0, ker0⟩ := quot_ex l L G0 T.H.toSubgroup ho (fun a ha => T.H_η a ha) (fun a ha => T.H_ε a ha)
  have hN : ∀ N, ∃ (G' : Glob l L) (g : (T.GN N).Hom G'), g.p.ker = PL l (T.H.toSubgroup.comap (T.h N).p) :=
    fun N => quot_ex l L (T.GN N) _ (hoN N)
      (fun a ha => show (T.GN N).η a = 1 by rw [← (T.h N).η]; exact T.H_η _ ha)
      (fun a ha => by rw [← (T.h N).ε]; exact T.H_ε _ ha)
  choose GN' gN kerN using hN
  have hmap : ∀ N, (gN N).p.ker.map (T.h N).p = g0.p.ker := fun N => by
    rw [kerN, ker0]
    exact pl_map l _ _ (T.h N).p T.H.toSubgroup ho (T.h N).cont (T.h N).surj
  have hd : ∀ N, ∃ h' : (GN' N).Hom G0', ∀ x, h'.p ((gN N).p x) = g0.p ((T.h N).p x) := fun N =>
    hom_desc l L _ _ _ _ (gN N) g0 (T.h N) fun a ha => by
      have : (T.h N).p a ∈ g0.p.ker := hmap N ▸ Subgroup.mem_map_of_mem _ ha
      exact this
  choose h' comm using hd
  obtain ⟨H', hH'⟩ := exists_desc g0 T.H (ker0 ▸ (pl_props l G0.Γ T.H.toSubgroup ho).2.2.1)
  haveI hn' : H'.toSubgroup.Normal := H'.isNormal'
  have ho' : IsOpen (H'.toSubgroup : Set G0'.Γ) := H'.toOpenSubgroup.isOpen
  have hiff : ∀ a, g0.p a ∈ H' ↔ a ∈ T.H := fun a => by
    show a ∈ H'.toSubgroup.comap g0.p ↔ a ∈ T.H.toSubgroup
    rw [hH']
  have hcN : ∀ N, (H'.toSubgroup.comap (h' N).p).comap (gN N).p = T.H.toSubgroup.comap (T.h N).p := fun N => by
    ext a
    show (h' N).p ((gN N).p a) ∈ H' ↔ (T.h N).p a ∈ T.H
    rw [comm, hiff]
  refine ⟨{ G0' := G0', g0 := g0, ker0 := ker0, GN' := GN', gN := gN, kerN := kerN, h' := h', comm := comm
            H' := H', H'_iff := hiff, ph_lim := fun V j => ?_, ker_le := fun N => ?_, fin0 := ?_
            finN := fun N => ?_, pl0 := ?_, plN := fun N => ?_ }⟩
  · let V' : OpenNormalSubgroup G0.Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap g0.p g0.cont
        isNormal' := Subgroup.Normal.comap V.isNormal' g0.p }
    refine T.ph_lim V' j fun a ha => ?_
    rw [← ker0, MonoidHom.mem_ker] at ha
    show g0.p a ∈ V.toSubgroup
    rw [ha]; exact one_mem _
  · intro x hx
    obtain ⟨a, rfl⟩ := (gN N).surj x
    have h1 : (T.h N).p a ∈ (gN N).p.ker.map (T.h N).p := by
      rw [hmap, MonoidHom.mem_ker, ← comm]; exact hx
    obtain ⟨b, hb, hba⟩ := h1
    have h2 : a * b⁻¹ ∈ (T.h N).p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, mul_inv_cancel]
    have h3 : (gN N).p a = (gN N).p (a * b⁻¹) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hb, inv_one, mul_one]
    rw [h3]
    have h4 : (Subgroup.normalClosure (Set.range fun j => (T.ta N j : (T.GN N).Γ)) ⊔
        PL l (T.H.toSubgroup.comap (T.h N).p)).topologicalClosure ≤
        (Subgroup.normalClosure (Set.range fun j => (gN N).p (T.ta N j))).topologicalClosure.comap (gN N).p := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        ((Subgroup.isClosed_topologicalClosure _).preimage (gN N).cont)
      · refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨j, rfl⟩
        exact Subgroup.subset_normalClosure ⟨j, rfl⟩
      · rw [← kerN]; exact MonoidHom.ker_le_comap _ _
    exact h4 (T.ker_le N h2)
  · exact (homl_desc l _ _ g0.p H'.toSubgroup g0.cont g0.surj (hH' ▸ T.fin0)).1
  · have := homl_desc l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (gN N).cont (gN N).surj
      (by rw [hcN]; exact (T.finN N).1)
    rw [hcN] at this
    exact ⟨this.1, this.2.trans (T.finN N).2⟩
  · rw [← pl_map l _ _ g0.p H'.toSubgroup ho' g0.cont g0.surj, hH', ← ker0, Subgroup.map_eq_bot_iff]
  · rw [← pl_map l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (ho'.preimage (h' N).cont) (gN N).cont (gN N).surj,
      hcN, ← kerN, Subgroup.map_eq_bot_iff]
