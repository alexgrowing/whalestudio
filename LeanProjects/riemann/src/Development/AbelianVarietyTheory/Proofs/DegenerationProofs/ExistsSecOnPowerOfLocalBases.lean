import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_resG_apply {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_secOn_glue {X : Scheme.{0}} (B : LB X) (V : X.Opens) {κ : Type} (T : κ → X.Opens)
    (hT : ∀ k, T k ≤ V) (hV : ∀ x ∈ V, ∃ k, x ∈ T k) (σ : ∀ k j, Γ(X, T k ⊓ B.U j))
    (hσ : ∀ k, σ k ∈ secOn B (T k))
    (hc : ∀ k k' j, resG X (inf_le_inf_right _ inf_le_left : (T k ⊓ T k') ⊓ B.U j ≤ T k ⊓ B.U j) (σ k j) =
      resG X (inf_le_inf_right _ inf_le_right : (T k ⊓ T k') ⊓ B.U j ≤ T k' ⊓ B.U j) (σ k' j)) :
    ∃ τ ∈ secOn B V, ∀ k j, resG X (inf_le_inf_right _ (hT k)) (τ j) = σ k j := by
  have H : ∀ j, ∃ τ : Γ(X, V ⊓ B.U j), ∀ k, resG X (inf_le_inf_right _ (hT k)) τ = σ k j := fun j => by
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun k => T k ⊓ B.U j) (V ⊓ B.U j)
      (fun k => homOfLE (inf_le_inf_right _ (hT k)))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hV x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hx.2⟩) (fun k => σ k j) (fun k k' => by
        have e : (T k ⊓ B.U j) ⊓ (T k' ⊓ B.U j) ≤ (T k ⊓ T k') ⊓ B.U j :=
          fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
        have := congrArg (resG X e) (hc k k' j)
        rw [resG_resG_apply, resG_resG_apply] at this
        exact this)
    exact ⟨g, hg⟩
  choose τ hτ using H
  refine ⟨τ, fun i j => ?_, fun k j => hτ j k⟩
  refine X.sheaf.eq_of_locally_eq' (fun k => T k ⊓ B.U i ⊓ B.U j) (V ⊓ B.U i ⊓ B.U j)
    (fun k => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hT k))))
    (fun x hx => by
      obtain ⟨k, hk⟩ := hV x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ⟨hk, hx.1.2⟩, hx.2⟩) _ _ fun k => ?_
  have h := hσ k i j
  rw [← hτ i k, ← hτ j k, resG_resG_apply, resG_resG_apply] at h
  change resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _ =
    resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _
  rw [map_mul, resG_resG_apply, resG_resG_apply, resG_resG_apply]
  exact h

theorem sum_mul_mem_secOn {X : Scheme.{0}} (B : LB X) (V : X.Opens) {I : Type} [Fintype I] (f : I → Γ(X, V))
    (σ : I → ∀ j, Γ(X, V ⊓ B.U j)) (hσ : ∀ i, σ i ∈ secOn B V) :
    (fun j => ∑ i, resG X inf_le_left (f i) * σ i j) ∈ secOn B V := fun j j' => by
  simp only [map_sum, map_mul, Finset.mul_sum, resG_resG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hσ i j j', mul_left_comm]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem ZHPre.genVal_res (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V V' : Q.G.left.Opens} (e : V' ≤ V)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V' (fun j => resG _ (inf_le_inf_right _ e) (σ j)) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  rw [h K β g r jP jL h1 h2 h3 h4 (h5.trans e)]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (V' ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact (valR_res (g ≫ Q.φ) _ hU _).symm

theorem ZHPre.genVal_of_cover (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V : Q.G.left.Opens} {κ : Type}
    (T : κ → Q.G.left.Opens) (hT : ∀ a, T a ≤ V) (hV : ∀ x ∈ V, ∃ a, x ∈ T a)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ a, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c (T a)
      (fun j => resG _ (inf_le_inf_right _ (hT a)) (σ j))) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  obtain ⟨a, ha⟩ := hV _ (h5 ⟨IsLocalRing.closedPoint K, rfl⟩)
  have h6 : Set.range (g ≫ Q.φ) ⊆ T a := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) w (IsLocalRing.closedPoint K)]
    exact ha
  rw [h a K β g r jP jL h1 h2 h3 h4 h6]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (T a ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h6 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact valR_res (g ≫ Q.φ) _ hU _

theorem ZHPre.genVal_sum (k : ℤ) {I J : Type} [Fintype I] [Fintype J]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : J → I → Ω) (W : M.Z.Opens)
    (hW : (W : Set M.Z).Nonempty) (f : J → Γ(M.Z, W))
    (σ : J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ i, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (c i) _ (σ i)) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (fun l => ∑ i, valF M.pt W (f i) * c i l) _
      (fun j => ∑ i, resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i)) * σ i j) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  have hV : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W) := fun w _ => h5 ⟨w, rfl⟩
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w, ← h1]
    rfl
  have hf : ∀ i, (valMap (g ≫ Q.φ) _ hU).hom (resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i))) =
      β (valF M.pt W (f i)) := fun i => by
    rw [← valR_eq, valR_res _ _ hU, valR_appLE _ _ _ hV, hp, valR_spMap_comp β M.pt W (M.top_le_preimage_pt hW),
      valF_eq_valR]
  have hi := fun i => h i K β g r jP jL h1 h2 h3 h4 h5
  rw [valF_eq_valR (g ≫ Q.φ), valR_eq _ _ hU, map_sum, Finset.mul_sum]
  simp only [map_sum, map_mul, Finset.sum_mul, hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← valR_eq, ← valF_eq_valR, ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

end GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_secOn_genVal_of_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  intro o Ω _ _ _ S ρ M U₀ EE Q hU hb W x₀ v hv
  have H : ∀ z : W, ∃ T : M.Z.Opens, z.1 ∈ T ∧ T ≤ W ∧
      ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ T),
        GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
    rintro ⟨z, hz⟩
    obtain ⟨U, b, hzU, -, hE⟩ := EE.loc z
    have h1 := (hv z hz).2
    rw [hE z hzU] at h1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun i l => b i l)).1 h1
    let T : M.Z.Opens := W ⊓ U ⊓ ⟨⋂ i, {z' | (a i : Ω) ∈ M.O z'},
      isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _⟩
    have hzT : z ∈ T := ⟨⟨hz, hzU⟩, Set.mem_iInter.2 fun i => (a i).2⟩
    have hne : (T : Set M.Z).Nonempty := ⟨z, hzT⟩
    have h2 : ∀ i, ∃ f : Γ(M.Z, T), valF M.pt T f = a i := fun i =>
      (RatModel.mem_ringOn_iff_exists hne).1 (RatModel.mem_ringOn.2 fun z' hz' => Set.mem_iInter.1 hz'.2 i)
    choose f hf using h2
    obtain ⟨σ, hσ⟩ := hb T x₀ b fun z' hz' => ⟨(hv z' hz'.1.1).1, hE z' hz'.1.2⟩
    refine ⟨T, hzT, inf_le_left.trans inf_le_left, _,
      sum_mul_mem_secOn _ _ (fun i => (Q.G.hom.appLE T _ le_rfl).hom (f i)) σ fun i => (hσ i).1, ?_⟩
    have h3 := Q.genVal_sum S.N ρ.s (fun i l => b i l / S.th x₀) T hne f σ fun i => (hσ i).2
    have h4 : (fun l => ∑ i, valF M.pt T (f i) * (b i l / S.th x₀)) = fun l => v l / S.th x₀ := by
      funext l
      rw [← ha, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← mul_div_assoc]
      rfl
    rw [h4] at h3
    exact h3
  choose T hz hT σ hσ hg using H
  have hle : ∀ z, Q.G.hom ⁻¹ᵁ T z ≤ Q.G.hom ⁻¹ᵁ W := fun z x hx => hT z hx
  have hcov : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ z, x ∈ Q.G.hom ⁻¹ᵁ T z := fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩
  obtain ⟨τ, hτ, hr⟩ := exists_secOn_glue _ (Q.G.hom ⁻¹ᵁ W) (fun z => Q.G.hom ⁻¹ᵁ T z) hle hcov σ hσ
    fun z z' j => congrFun (Q.eq_of_genVal hU _ _ _ _ _ _ (Q.genVal_res _ _ _ inf_le_left _ (hg z))
      (Q.genVal_res _ _ _ inf_le_right _ (hg z'))) j
  refine ⟨τ, hτ, Q.genVal_of_cover _ _ _ _ hle hcov τ fun z => ?_⟩
  have h5 := hg z
  rw [← funext (hr z)] at h5
  exact h5

end GlobalTheory.ZH
