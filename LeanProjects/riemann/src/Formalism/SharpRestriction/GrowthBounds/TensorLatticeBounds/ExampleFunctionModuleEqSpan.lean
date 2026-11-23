import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataRank

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P)

theorem mem_funMod (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = ((C.χ γ : Oˣ) : O) • C.actX γ (F L) := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply,
    and_assoc, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply,
    sub_eq_zero]

end Gen

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def tup0 (h : HidaSetting p n' W Qq O Kf ι σ j w) : (places1 h).Tup := fun _ => line W p 0

theorem zero_tuple_isLattice (h : HidaSetting p n' W Qq O Kf ι σ j w) : (places1 h).IsLatTup (tup0 h) := fun _ => line_isLattice h 0

theorem tup_eq_smul (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : (places1 h).Tup) (hL : (places1 h).IsLatTup L) :
    ∃ γ : (level1 h).Γ, L = (level1 h).smul γ (tup0 h) := by
  obtain ⟨n, hn⟩ := lat1 h (L (0 : Fin 1)) (hL (0 : Fin 1))
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  funext v
  have hv : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) v 0
  subst hv
  have h1 := smul1 h (Multiplicative.ofAdd n) (tup0 h) 0 rfl
  refine hn.trans (Eq.trans ?_ h1.symm)
  simp

theorem funMod_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) (Hv : (places1 h).Tup → Submodule O (places1 h).Xsp)
    (h1 : ∀ L, (1 : (places1 h).Xsp) ∈ Hv L)
    (h2 : ∀ L, (places1 h).IsLatTup L → Hv L ≤ Submodule.span O {1}) :
    (level1 h).funMod Hv = Submodule.span O {oneFn (places1 h)} := by
  apply le_antisymm
  · intro F hF
    obtain ⟨a1, a2, a3⟩ := (mem_funMod (level1 h) Hv F).1 hF
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h2 _ (zero_tuple_isLattice h) (a1 _ (zero_tuple_isLattice h)))
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    funext L
    by_cases hL : (places1 h).IsLatTup L
    · obtain ⟨γ, rfl⟩ := tup_eq_smul h L hL
      rw [a3, ← hc, Pi.smul_apply, oneFn_pos _ hL, LinearMap.map_smul_of_tower]
      have hx : (level1 h).actX γ 1 = 1 := natAct_one' (places1 h) (fun _ => rfl) _
      rw [hx]
      show c • (1 : (places1 h).Xsp) = (((1 : Oˣ) : O)) • c • (1 : (places1 h).Xsp)
      rw [Units.val_one, one_smul]
    · rw [a2 L hL, Pi.smul_apply, oneFn_neg _ hL, smul_zero]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact oneFn_mem (places1 h) (level1 h) (fun _ => rfl) rfl Hv h1

def oneG (h : HidaSetting p n' W Qq O Kf ι σ j w) : (gat1 h).Fn := fun _ => oneFn (places1 h)

theorem example_function_module_eq_span (h : HidaSetting p n' W Qq O Kf ι σ j w) (Hv : (places1 h).Tup → Submodule O (places1 h).Xsp)
    (h1 : ∀ L, (1 : (places1 h).Xsp) ∈ Hv L)
    (h2 : ∀ L, (places1 h).IsLatTup L → Hv L ≤ Submodule.span O {1}) :
    (gat1 h).funMod Hv = Submodule.span (gat1 h).O {oneG h} := by
  ext F
  unfold GAtP.funMod
  rw [Submodule.mem_pi, Submodule.mem_span_singleton]
  constructor
  · intro hF
    have := hF () (Set.mem_univ _)
    have h3 : (show (places1 h).Tup → (places1 h).Xsp from F ()) ∈ (level1 h).funMod Hv := this
    rw [funMod_eq h Hv h1 h2] at h3
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h3
    exact ⟨c, funext fun _ => hc⟩
  · rintro ⟨c, rfl⟩ i _
    show (show O from c) • oneFn (places1 h) ∈ (level1 h).funMod Hv
    rw [funMod_eq h Hv h1 h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem finrank_oneG (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    Module.finrank (gat1 h).O (Submodule.span (gat1 h).O {oneG h}) = 1 := by
  have := h.frac_O
  have hf : Function.Injective (LinearMap.toSpanSingleton (gat1 h).O (gat1 h).Fn (oneG h)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : (show O from c) • (oneFn (places1 h) (tup0 h)) = 0 := congrFun (congrFun hc ()) (tup0 h)
    rw [oneFn_pos _ (zero_tuple_isLattice h), Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply] at h1
    have h2 : algebraMap O Kf (show O from c) = 0 := by
      have := congrArg constantCoeff h1
      simpa using this
    exact (map_eq_zero_iff _ (IsFractionRing.injective O Kf)).1 h2
  rw [LinearMap.span_singleton_eq_range, LinearMap.finrank_range_of_inj hf, Module.finrank_self]

theorem example_dual_module_eq_span_one (h : HidaSetting p n' W Qq O Kf ι σ j w) : (gat1 h).Mna = Submodule.span (gat1 h).O {oneG h} :=
  example_function_module_eq_span h _ (one_mem_Htup (places1 h) fun _ => rfl) (Htup_le_const (gat1 h) fun _ => rfl)

theorem example_module_eq_span_one (h : HidaSetting p n' W Qq O Kf ι σ j w) : (gat1 h).M = Submodule.span (gat1 h).O {oneG h} :=
  example_function_module_eq_span h _ (one_mem_HtupW (places1 h) fun _ => rfl) (HtupW_le_const (gat1 h) fun _ => rfl)

theorem example_rank_one_sandwich (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    (gat1 h).M = (gat1 h).Mna ∧ (gat1 h).d = 1 ∧ (gat1 h).dna = 1 ∧ (gat1 h).Sandwich := by
  have hM := example_module_eq_span_one h
  have hN := example_dual_module_eq_span_one h
  refine ⟨hM.trans hN.symm, ?_, ?_, ?_, ?_⟩
  · unfold GAtP.d; rw [hM]; exact finrank_oneG h
  · unfold GAtP.dna; rw [hN]; exact finrank_oneG h
  · rw [hM, hN]
    show Submodule.map (((p : (gat1 h).O) ^ 0) • LinearMap.id) _ ≤ _
    rw [pow_zero, one_smul, Submodule.map_id]
  · rw [hM, hN]

theorem gat_full_nonempty (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n' : ℕ) (h2 : 2 ≤ n') (he : Even n') :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ G.P.r = 1 ∧ G.TrivStab ∧ G.FinClasses ∧ G.d = 1 ∧ G.dna = 1 ∧ G.Sandwich ∧
      ∀ v, G.P.n' v = n' ∧
        UnramifiedQuadraticSetting p (G.P.n' v) (G.P.W v) (G.P.Qq v) G.O G.Kf (G.P.ι v) (G.P.σ v) (G.P.j v) G.P.w ∧
        LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
          (G.P.lam0 v) 0 0 0 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hS := Formalism.L2.G.settingStd p n' h5 h2 he
  have h := hS.1
  obtain ⟨-, h3, h4, h5'⟩ := example_rank_one_sandwich h
  exact ⟨gat1 h, le_rfl, rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, h3, h4, h5',
    fun _ => ⟨rfl, hS, lpprime_zero h⟩⟩

theorem dimV_eq_one (K : Type) [Field K] {n' m : ℕ} : dimV K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) = 1 := by
  apply le_antisymm (dimV_le_one K)
  unfold dimV
  have : FiniteDimensional K ↥(Vsp K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ)) :=
    Submodule.finiteDimensional_of_le (Vsp_le K)
  rw [Nat.succ_le_iff, Module.finrank_pos_iff_exists_ne_zero]
  exact ⟨⟨1, one_mem_Vsp K⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩

end Formalism.MainNotions.G.Inhab

end
