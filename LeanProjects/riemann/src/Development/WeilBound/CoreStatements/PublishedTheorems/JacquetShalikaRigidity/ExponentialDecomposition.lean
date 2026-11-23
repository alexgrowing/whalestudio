import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ExponentialDecomposition

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  apply Units.ext
  rw [Iwasawa.coe_torusPow]
  simp

theorem exp_one : Iwasawa.iwasawaExponent F n 1 = 0 := by
  have := Iwasawa.iwasawaExponent_torusPow F n 0
  rwa [torusPow_zero] at this

theorem exp_of_mem {κ : GL (Fin n) F} (hκ : κ ∈ GLnLocal.integralGL F n) :
    Iwasawa.iwasawaExponent F n κ = 0 := by
  have := Iwasawa.iwasawaExponent_mul_of_mem_integralGL F n 1 hκ
  rw [one_mul, exp_one] at this
  exact this

theorem isOpen_exp (A : Set (Fin n → ℤ)) :
    IsOpen {x : GL (Fin n) F | Iwasawa.iwasawaExponent F n x ∈ A} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F)), ?_, ?_, ?_⟩
  · intro y hy
    have e : y = x * (x⁻¹ * y) := by group
    show Iwasawa.iwasawaExponent F n y ∈ A
    rw [e, Iwasawa.iwasawaExponent_mul_of_mem_integralGL F n x hy]
    exact hx
  · exact (GLnLocal.isOpen_integralGL F n).preimage (continuous_const_mul _)
  · show x⁻¹ * x ∈ GLnLocal.integralGL F n
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClopen_exp (l : Fin n → ℤ) : IsClopen {x : GL (Fin n) F | Iwasawa.iwasawaExponent F n x = l} :=
  ⟨isOpen_compl_iff.1 (isOpen_exp F n {l}ᶜ), isOpen_exp F n {l}⟩

end Loc

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mem_int_iff (w : Pl E) (x : w.adicCompletion E) :
    x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer ↔ x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem corner_entry {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (g : GL (Fin k) R) (i c : Fin k)
    (h : g.val i c = (1 : Matrix (Fin k) (Fin k) R) i c) :
    (cornerGL k s g).val i c = (1 : Matrix (Fin k) (Fin k) S) i c := by
  change (1 : Matrix (Fin k) (Fin k) S) i c - s ((1 : Matrix (Fin k) (Fin k) R) i c) + s (g.val i c) = _
  rw [h, sub_add_cancel]

theorem uu_one : UU 0 (1 : GA E k) :=
  ⟨fun i c h => by rw [Units.val_one, Matrix.one_apply_ne h.ne'], fun i => by rw [Units.val_one, Matrix.one_apply_eq],
    fun i c h => absurd h (Nat.not_lt_zero _)⟩

theorem uu_mul {g h : GA E k} (hg : UU 0 g) (hh : UU 0 h) : UU 0 (g * h) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j i with hj | hj
    · rw [hg.1 i j hj, zero_mul]
    · rw [hh.1 j c (lt_of_lt_of_le hci hj), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hg.2.1, hh.2.1, one_mul]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hg.1 i j hj, zero_mul]
      · rw [hh.1 j i hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem uu_fl (w : Pl E) {n : GL (Fin k) (w.adicCompletion E)} (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k) :
    UU 0 (fl k w n) := by
  have key : ∀ i c : Fin k, c ≤ i → (fl k w n).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c := by
    intro i c hci
    show (cornerGL k (sFin E) (cornerGL k (sLoc E w) n)).val i c = _
    refine corner_entry _ _ _ _ (corner_entry _ _ _ _ ?_)
    rcases hci.lt_or_eq with h | h
    · rw [hn.1 h, Matrix.one_apply_ne h.ne']
    · subst h
      rw [hn.2, Matrix.one_apply_eq]
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [key i c h.le, Matrix.one_apply_ne h.ne']
  · rw [key i i le_rfl, Matrix.one_apply_eq]

theorem cLoc_uu {u : GA E k} (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent (w.adicCompletion E) k := by
  refine ⟨fun i c h => ?_, fun i => ?_⟩
  · show ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c h, map_zero]
  · show ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

def Gd (g : GA E k) (w : Pl E) : Prop :=
  ∀ i j, (pFin E (g.val i j)).1 w ∈ w.adicCompletionIntegers E ∧
    (pFin E ((g⁻¹ : GA E k).val i j)).1 w ∈ w.adicCompletionIntegers E

theorem gd_fin (g : GA E k) : {w | ¬ Gd g w}.Finite := by
  have h : ∀ᶠ w in cofinite, Gd g w := by
    unfold Gd
    simp only [Filter.eventually_all]
    intro i j
    exact (pFin E (g.val i j)).2.and (pFin E ((g⁻¹ : GA E k).val i j)).2
  exact Filter.eventually_cofinite.1 h

theorem gd_mem {g : GA E k} {w : Pl E} (h : Gd g w) : cLoc w g ∈ GLnLocal.integralGL (w.adicCompletion E) k := by
  rw [GLnLocal.mem_integralGL_iff]
  refine ⟨fun i j => (mem_int_iff w _).2 (h i j).1, fun i j => ?_⟩
  rw [← map_inv]
  exact (mem_int_iff w _).2 (h i j).2

theorem isOpen_gd (T : Set (Pl E)) : IsOpen {g : GA E k | ∀ w, w ∉ T → Gd g w} := by
  let V : Set (Af E) := {x | ∀ w, w ∉ T → x.1 w ∈ w.adicCompletionIntegers E}
  have hV : IsOpen V := RestrictedProduct.isOpen_forall_imp_mem (fun w => GroundTheory.Global.isOpen_adicCompletionIntegers w)
  have e : {g : GA E k | ∀ w, w ∉ T → Gd g w} = ⋂ i, ⋂ j,
      ((fun g : GA E k => pFin E (g.val i j)) ⁻¹' V ∩ (fun g : GA E k => pFin E ((g⁻¹ : GA E k).val i j)) ⁻¹' V) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, V, Gd]
    exact ⟨fun h i j => ⟨fun w hw => (h w hw i j).1, fun w hw => (h w hw i j).2⟩,
      fun h w hw i j => ⟨(h i j).1 w hw, (h i j).2 w hw⟩⟩
  rw [e]
  have hp : Continuous (pFin E) := continuous_snd
  have hv : Continuous (fun g : GA E k => (g.val : Matrix (Fin k) (Fin k) (Ad E))) := Units.continuous_val
  have hw : Continuous (fun g : GA E k => ((g⁻¹ : GA E k).val : Matrix (Fin k) (Fin k) (Ad E))) :=
    Units.continuous_coe_inv
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact hV.preimage (hp.comp (hv.matrix_elem i j))
  · exact hV.preimage (hp.comp (hw.matrix_elem i j))

theorem isOpen_G0 (hG : jumpWindows.G0) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}
    (S : Finset (Pl E)) : IsOpen (G0 (k := k) S) := by
  have hcont : ∀ w, Continuous (cLoc w : GA E k → _) := (hG E k).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  have hT : {w | ¬ Gd g w ∧ w ∉ S}.Finite := (gd_fin g).subset fun w hw => hw.1
  refine ⟨{h | ∀ w, w ∉ {w | ¬ Gd g w} → Gd h w} ∩
    ⋂ w ∈ {w | ¬ Gd g w ∧ w ∉ S}, (cLoc w) ⁻¹' {x | Iwasawa.iwasawaExponent _ k x = 0}, ?_, ?_, ?_⟩
  · rintro h ⟨h1, h2⟩ w hw
    by_cases hg' : Gd g w
    · exact exp_of_mem _ _ (gd_mem (h1 w fun h => h hg'))
    · exact Set.mem_iInter₂.1 h2 w ⟨hg', hw⟩
  · exact (isOpen_gd _).inter (hT.isOpen_biInter fun w _ => (isOpen_exp _ k {0}).preimage (hcont w))
  · refine ⟨fun w hw => not_not.1 hw, Set.mem_iInter₂.2 fun w hw => hg w hw.2⟩

theorem decomp (hG : jumpWindows.G0) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}
    (S T : Finset (Pl E)) : ∀ g : GA E k, (∀ w, w ∉ S → Iwasawa.iwasawaExponent _ k (cLoc w g) = 0) →
      (∀ w, w ∉ S → w ∉ T → cLoc w g ∈ GLnLocal.integralGL (w.adicCompletion E) k) →
      ∃ n g₀ κ : GA E k, UU 0 n ∧ InS S g₀ ∧ cInf κ = 1 ∧ (∀ w ∈ S, cLoc w κ = 1) ∧
        (∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) ∧ g = n * g₀ * κ := by
  obtain ⟨-, -, -, hloc, hlocne, -, -, -, -, -, hsplit, -⟩ := hG E k
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g _ hK
    obtain ⟨g₀, h1, h2, h3⟩ := hsplit S g
    refine ⟨1, g₀, g₀⁻¹ * g, uu_one, h3, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_inv, h1, inv_mul_cancel]
    · intro w hw
      rw [map_mul, map_inv, h2 w hw, inv_mul_cancel]
    · intro w
      by_cases hw : w ∈ S
      · rw [map_mul, map_inv, h2 w hw, inv_mul_cancel]
        exact one_mem _
      · rw [map_mul, map_inv, h3 w hw, inv_one, one_mul]
        exact hK w hw (Finset.notMem_empty w)
    · group
  | insert v T hvT ih =>
    intro g hexp hK
    by_cases hvS : v ∈ S
    · refine ih g hexp fun w hw hwT => hK w hw fun h => ?_
      rcases Finset.mem_insert.1 h with h | h
      · exact hw (h ▸ hvS)
      · exact hwT h
    · obtain ⟨u, hu, κ, hκ, he⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc v g)
      rw [hexp v hvS, torusPow_zero, mul_one] at he
      have hloc' : ∀ w, w ≠ v → cLoc w ((fl k v u)⁻¹ * g) = cLoc w g := by
        intro w hw
        rw [map_mul, map_inv, hlocne v w u hw, inv_one, one_mul]
      have hv' : cLoc v ((fl k v u)⁻¹ * g) = κ := by
        rw [map_mul, map_inv, hloc v u, he, inv_mul_cancel_left]
      obtain ⟨n, g₀, κ', hn, h1, h2, h3, h4, h5⟩ := ih ((fl k v u)⁻¹ * g)
        (fun w hw => by
          by_cases hwv : w = v
          · subst hwv
            rw [hv']
            exact exp_of_mem _ _ hκ
          · rw [hloc' w hwv]
            exact hexp w hw)
        (fun w hw hwT => by
          by_cases hwv : w = v
          · subst hwv
            rw [hv']
            exact hκ
          · rw [hloc' w hwv]
            exact hK w hw fun h => (Finset.mem_insert.1 h).elim hwv hwT)
      refine ⟨fl k v u * n, g₀, κ', uu_mul (uu_fl v hu) hn, h1, h2, h3, h4, ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_assoc n, ← h5, ← mul_assoc, mul_inv_cancel, one_mul]

end ExponentialDecomposition

theorem open_decomposition_of_G0 : jumpWindows.G0 → C0 := by
  intro hG E _ _ _ k S
  have hGk := hG E k
  obtain ⟨-, -, hinf1, hloc, hlocne, -, -, -, -, -, -, -, hcont, -⟩ := hGk
  refine ⟨ExponentialDecomposition.isOpen_G0 hG S, fun w _ => by rw [map_one]; exact ExponentialDecomposition.exp_one _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro u g hu
    constructor
    · intro h w hw
      rw [← h w hw, map_mul, Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ _ (ExponentialDecomposition.cLoc_uu hu w)]
    · intro h w hw
      rw [map_mul, Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ _ (ExponentialDecomposition.cLoc_uu hu w)]
      exact h w hw
  · intro g hg
    classical
    exact ExponentialDecomposition.decomp hG S (ExponentialDecomposition.gd_fin g).toFinset g hg fun w _ hwT =>
      ExponentialDecomposition.gd_mem (not_not.1 fun h => hwT ((ExponentialDecomposition.gd_fin g).mem_toFinset.2 h))
  · intro g
    refine (ExponentialDecomposition.gd_fin g).subset fun w hw => ?_
    intro h
    exact hw (ExponentialDecomposition.exp_of_mem _ _ (ExponentialDecomposition.gd_mem h))
  · intro w l
    exact (ExponentialDecomposition.isClopen_exp _ k l).preimage (hcont w)
  · intro w g
    refine ⟨g * (fl k w (cLoc w g))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_inv, hloc, mul_inv_cancel]
    · group
    · rw [map_mul, map_inv, hinf1, inv_one, mul_one]
    · intro v hv
      rw [map_mul, map_inv, hlocne w v _ hv, inv_one, mul_one]

end PositivityTheory.AdelicQuotientData

end
