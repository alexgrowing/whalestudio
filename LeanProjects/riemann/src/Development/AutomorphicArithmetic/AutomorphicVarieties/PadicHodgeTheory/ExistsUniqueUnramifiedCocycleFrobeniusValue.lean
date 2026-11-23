import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.UnramifiedCocycles

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

private def SD (_ρ : Representation A G V) : Type := V × G

private instance instGroupSD (ρ : Representation A G V) : Group (SD ρ) where
  mul p q := (p.1 + ρ p.2 q.1, p.2 * q.2)
  one := (0, 1)
  inv p := (-(ρ p.2⁻¹ p.1), p.2⁻¹)
  mul_assoc p q r := by
    refine Prod.ext ?_ (mul_assoc p.2 q.2 r.2)
    change p.1 + ρ p.2 q.1 + ρ (p.2 * q.2) r.1 = p.1 + ρ p.2 (q.1 + ρ q.2 r.1)
    simp [add_assoc]
  one_mul p := by
    refine Prod.ext ?_ (one_mul p.2)
    change (0 : V) + ρ 1 p.1 = p.1
    simp
  mul_one p := by
    refine Prod.ext ?_ (mul_one p.2)
    change p.1 + ρ p.2 0 = p.1
    simp
  inv_mul_cancel p := by
    refine Prod.ext ?_ (inv_mul_cancel p.2)
    change -(ρ p.2⁻¹ p.1) + ρ p.2⁻¹ p.1 = 0
    simp

private instance instTopSD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V] :
    TopologicalSpace (SD ρ) := inferInstanceAs (TopologicalSpace (V × G))

private theorem topGroup_SD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalGroup G] [IsTopologicalAddGroup V] (h : ContAction ρ) : IsTopologicalGroup (SD ρ) := by
  have hm : Continuous fun x : (V × G) × (V × G) => ((x.1.1 + ρ x.1.2 x.2.1, x.1.2 * x.2.2) : V × G) :=
    (continuous_fst.fst.add (h.comp (continuous_fst.snd.prodMk continuous_snd.fst))).prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have hi : Continuous fun x : V × G => ((-(ρ x.2⁻¹ x.1), x.2⁻¹) : V × G) :=
    (h.comp (continuous_snd.inv.prodMk continuous_fst)).neg.prodMk continuous_snd.inv
  exact { continuous_mul := hm, continuous_inv := hi }

private def SDsub (ρ : Representation A G V) (L : AddSubgroup V) (hL : ∀ g, ∀ y ∈ L, ρ g y ∈ L) :
    Subgroup (SD ρ) where
  carrier := {p | p.1 ∈ L}
  mul_mem' := fun {p q} hp hq => L.add_mem hp (hL _ _ hq)
  one_mem' := L.zero_mem
  inv_mem' := fun {p} hp => L.neg_mem (hL _ _ hp)

private theorem all_of_closed [TopologicalSpace G] [IsTopologicalGroup G] {I : Subgroup G} {σ : G}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : G) : g ∈ H := by
  have h1 : I ⊔ Subgroup.zpowers σ ≤ H := sup_le hI (Subgroup.zpowers_le.2 hσ)
  have h2 := Subgroup.topologicalClosure_minimal _ h1 hH
  rw [hd] at h2
  exact h2 (Subgroup.mem_top g)

private theorem exists_lattice {l : ℕ} [Fact l.Prime] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [TopologicalSpace G] [CompactSpace G] (ρ : Representation A G V) (h : ContAction ρ) (x : V) :
    T2Space V ∧ TotallyDisconnectedSpace V ∧
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ x ∈ L ∧ ∀ g, ∀ y ∈ L, ρ g y ∈ L := by
  let e : V ≃ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := (Module.finBasis ℚ_[l] V).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  let E : V ≃ₜ (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) :=
    { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := he' }
  have hT2 : T2Space V := E.isEmbedding.t2Space
  have hTD : TotallyDisconnectedSpace V :=
    E.isEmbedding.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  refine ⟨hT2, hTD, ?_⟩
  have hρc : ∀ g : G, Continuous fun v : V => ρ g v :=
    fun g => h.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Set.range fun g : G => e (ρ g x)) :=
    isCompact_range (he.comp (h.comp (continuous_id.prodMk continuous_const)))
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  have hr1 : Set.range (fun g : G => e (ρ g x)) ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let M := (IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank ℚ_[l] V) → ℚ_[l])
    (lt_of_lt_of_le one_pos (le_max_right r 1))).toAddSubgroup
  have hM : ∀ y, y ∈ M ↔ y ∈ Metric.closedBall (0 : Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) (max r 1) :=
    fun y => Iff.rfl
  let L : AddSubgroup V := ⨅ g : G, M.comap ((e.toLinearMap.toAddMonoidHom).comp (ρ g).toAddMonoidHom)
  have hL : ∀ v, v ∈ L ↔ ∀ g, e (ρ g v) ∈ Metric.closedBall 0 (max r 1) := by
    intro v
    simp only [L, AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hM]
    rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · have hcl : IsClosed (L : Set V) := by
      have : (L : Set V) = ⋂ g : G, (fun v => e (ρ g v)) ⁻¹' Metric.closedBall 0 (max r 1) := by
        ext v
        simp only [SetLike.mem_coe, hL, Set.mem_iInter, Set.mem_preimage]
      rw [this]
      exact isClosed_iInter fun g => Metric.isClosed_closedBall.preimage (he.comp (hρc g))
    have hsub : (L : Set V) ⊆ E ⁻¹' Metric.closedBall 0 (max r 1) := by
      intro v hv
      have := (hL v).1 hv 1
      simpa [E] using this
    exact (E.isCompact_preimage.2 (isCompact_closedBall _ _)).of_isClosed_subset hcl hsub
  · exact (hL x).2 fun g => hr1 ⟨g, rfl⟩
  · intro g y hy
    refine (hL _).2 fun k => ?_
    have := (hL y).1 hy (k * g)
    simpa [map_mul] using this

end UpperTheory.V.Loc.UnramifiedCocycles

open UpperTheory.V.Loc.UnramifiedCocycles in
theorem UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A (GQ v) V), ContAction ρ → (∀ g ∈ Iq v, ρ g = 1) → ∀ σ : GQ v, IsFrob σ → ∀ x : V, ∃! c : GQ v → V, c ∈ Z1 ρ ∧ (∀ g ∈ Iq v, c g = 0) ∧ c σ = x := by
  intro v l _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hc hI σ hσ x
  obtain ⟨hT2, hTD, L, hLc, hxL, hLs⟩ := exists_lattice (l := l) ρ hc x
  haveI : IsTopologicalGroup (SD ρ) := topGroup_SD ρ hc
  haveI : T2Space (SD ρ) := inferInstanceAs (T2Space (V × GQ v))
  haveI : TotallyDisconnectedSpace (SD ρ) := inferInstanceAs (TotallyDisconnectedSpace (V × GQ v))
  have hS : IsCompact ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) := by
    have h0 : IsCompact ((L : Set V) ×ˢ (Set.univ : Set (GQ v))) := hLc.prod isCompact_univ
    have e0 : ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) =
        ((L : Set V) ×ˢ (Set.univ : Set (GQ v)) : Set (V × GQ v)) := by
      ext p
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [e0]
    exact h0
  haveI : CompactSpace (SDsub ρ L hLs) := isCompact_iff_compactSpace.1 hS
  obtain ⟨f, hfc, hf1, hfσ⟩ := frobFree σ hσ (SDsub ρ L hLs) ⟨((x, σ) : V × GQ v), hxL⟩
  have hfv : Continuous fun g => ((f g : SD ρ)) := continuous_subtype_val.comp hfc
  have hmul : ∀ g h, ((f (g * h) : SD ρ)) = (f g : SD ρ) * (f h : SD ρ) := fun g h => by
    rw [map_mul]
    rfl
  let k : GQ v → GQ v := fun g => ((f g : SD ρ)).2
  have hk1 : k 1 = 1 := by
    show ((f 1 : SD ρ)).2 = 1
    rw [map_one]
    rfl
  have hkm : ∀ a b, k (a * b) = k a * k b := fun a b => by
    show ((f (a * b) : SD ρ)).2 = _
    rw [hmul]
    rfl
  have hki : ∀ a, k a⁻¹ = (k a)⁻¹ := fun a => by
    have : k a⁻¹ * k a = 1 := by rw [← hkm, inv_mul_cancel, hk1]
    exact eq_inv_of_mul_eq_one_left this
  have hkc : Continuous k := continuous_snd.comp hfv
  have hgw : ∀ w : V, Continuous fun g : GQ v => ρ g w := fun w => hc.comp (continuous_id.prodMk continuous_const)
  have happ : ∀ (g : GQ v) (w : V), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have happ' : ∀ (g : GQ v) (w : V), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let H : Subgroup (GQ v) :=
    { carrier := {g | ∀ w, ρ (k g) w = ρ g w}
      one_mem' := fun w => by simp [hk1]
      mul_mem' := fun {a b} ha hb w => by
        simp only [Set.mem_setOf_eq] at ha hb
        rw [hkm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha w => by
        simp only [Set.mem_setOf_eq] at ha
        rw [hki]
        calc ρ (k a)⁻¹ w = ρ (k a)⁻¹ (ρ a (ρ a⁻¹ w)) := by rw [happ]
          _ = ρ (k a)⁻¹ (ρ (k a) (ρ a⁻¹ w)) := by rw [ha]
          _ = ρ a⁻¹ w := happ' _ _ }
  have hH : IsClosed (H : Set (GQ v)) := by
    have e1 : (H : Set (GQ v)) = ⋂ w : V, {g | ρ (k g) w = ρ g w} := by
      ext g
      simp [H]
    rw [e1]
    exact isClosed_iInter fun w => isClosed_eq ((hgw w).comp hkc) (hgw w)
  have hIH : Iq v ≤ H := fun g hg w => by
    show ρ ((f g : SD ρ)).2 w = ρ g w
    rw [hf1 g hg, hI g hg]
    show ρ (1 : GQ v) w = (1 : Module.End A V) w
    simp
  have hσH : σ ∈ H := fun w => by
    show ρ ((f σ : SD ρ)).2 w = ρ σ w
    rw [hfσ]
  have hk : ∀ g w, ρ (k g) w = ρ g w := fun g => all_of_closed (frobDense σ hσ) H hH hIH hσH g
  let c : GQ v → V := fun g => ((f g : SD ρ)).1
  have ccont : Continuous c := continuous_fst.comp hfv
  have cco : ∀ g h, c (g * h) = c g + ρ g (c h) := fun g h => by
    show ((f (g * h) : SD ρ)).1 = ((f g : SD ρ)).1 + ρ g ((f h : SD ρ)).1
    rw [hmul]
    exact congrArg (((f g : SD ρ)).1 + ·) (hk g _)
  have cI : ∀ g ∈ Iq v, c g = 0 := fun g hg => by
    show ((f g : SD ρ)).1 = 0
    rw [hf1 g hg]
    rfl
  have cσ : c σ = x := by
    show ((f σ : SD ρ)).1 = x
    rw [hfσ]
  have h1 : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → d 1 = 0 := fun d hd => by
    have := hd 1 1
    simpa using this
  have hinv : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → ∀ g, d g⁻¹ = -(ρ g⁻¹ (d g)) :=
    fun d hd g => by
      have := hd g⁻¹ g
      rw [inv_mul_cancel, h1 d hd] at this
      exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨c, ⟨⟨ccont, cco⟩, cI, cσ⟩, ?_⟩
  rintro c' ⟨hZ, hc'I, hc'σ⟩
  obtain ⟨c'cont, c'co⟩ : Continuous c' ∧ ∀ g h, c' (g * h) = c' g + ρ g (c' h) := hZ
  let H' : Subgroup (GQ v) :=
    { carrier := {g | c' g = c g}
      one_mem' := by
        show c' 1 = c 1
        rw [h1 c' c'co, h1 c cco]
      mul_mem' := fun {a b} ha hb => by
        show c' (a * b) = c (a * b)
        rw [c'co, cco, show c' a = c a from ha, show c' b = c b from hb]
      inv_mem' := fun {a} ha => by
        show c' a⁻¹ = c a⁻¹
        rw [hinv c' c'co, hinv c cco, show c' a = c a from ha] }
  have hH' : IsClosed (H' : Set (GQ v)) := isClosed_eq c'cont ccont
  have hIH' : Iq v ≤ H' := fun g hg => by
    show c' g = c g
    rw [hc'I g hg, cI g hg]
  have hσH' : σ ∈ H' := by
    show c' σ = c σ
    rw [hc'σ, cσ]
  funext g
  exact all_of_closed (frobDense σ hσ) H' hH' hIH' hσH' g
