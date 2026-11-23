import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EvenPull

theorem pmaps_of_section {X X' Y Y' S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (π : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ π = 𝟙 _) (hp : Function.Surjective π.appTop.hom)
    (H : ∀ y J J', Good L y J → Good L' y J' → val t (e ≫ h) y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique' hL (φ := fun k => h ≫ φ k) (ε := ε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ ε I) (hψ I))
    π e he hp (DVR.pullGen_isGen _ _ _ _ ht h) ht₁ (fun y J hJ => by
      choose J' hJ' using fun χ : S₀ ⟶ X' => exists_chart hL' (χ y)
      refine (val_pull hJ _ _ _).trans ((H y J J' hJ hJ').trans (Eq.trans ?_
        (hv _ e y _ _ (hJ.mem _ e) (Good.mem hJ' _ e)).symm))
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl
      rw [Category.assoc])
  intro Z r z p q hp hq
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have m₁ : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  have m₂ : (r ≫ h) z ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k =>
    (congrArg (fun g => g (r z) ∈ L.U (p k)) (hψ k)).mp (hp k)
  have c₁ := gen_trans ht (r ≫ h) z m₂ (Good.mem hJ _ _)
  have c₂ := gen_trans ht₁ r z m₁ (Good.mem hJ _ _)
  have c₃ : trF φ ε (r ≫ h) z p (fun k => J ((r ≫ h) ≫ φ k)) =
      trF (fun k => φ' k ≫ F) ε r z p (fun k => J (r ≫ φ' k ≫ F)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (r ≫ h) ≫ φ k = r ≫ φ' k ≫ F := by rw [hψ, Category.assoc]
    show gm ((r ≫ h) ≫ φ k) z (L.U (p k) ⊓ L.U (J ((r ≫ h) ≫ φ k))) (L.g (p k) (J ((r ≫ h) ≫ φ k))) ^ _ =
      gm (r ≫ φ' k ≫ F) z (L.U (p k) ⊓ L.U (J (r ≫ φ' k ≫ F))) (L.g (p k) (J (r ≫ φ' k ≫ F))) ^ _
    rw [this]
  have c₄ : val t (r ≫ h) z J = val t₁ r z J := (val_pull hJ _ _ _).symm.trans (key Z r z J hJ)
  exact c₁.trans ((congrArg₂ (· * ·) c₃ c₄).trans (c₂.symm.trans (hv Z r z p q m₁ (Set.mem_iInter.2 hq))))

theorem inv_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (ι[(Over.pullback f).obj G]).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Functor.obj.ι_def]
  exact pullback.lift_fst _ _ _

theorem inv_left_comp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (b : G' ⟶ G) [IsMonHom b] :
    (ι[G']).left ≫ b.left = b.left ≫ (ι[G]).left := by
  rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]

theorem inv_hom_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (b : G' ⟶ (Over.pullback f).obj G) [IsMonHom b] :
    (ι[G']).left ≫ b.left ≫ pullback.fst G.hom f = (b.left ≫ pullback.fst G.hom f) ≫ (ι[G]).left := by
  rw [← Category.assoc, inv_left_comp b, Category.assoc, Category.assoc]
  exact congrArg (b.left ≫ ·) (inv_fst f G)

theorem eSec_inv {S : Scheme.{0}} (H : Over S) [GrpObj H] : eSec H ≫ (ι[H]).left = eSec H := by
  rw [eSec, ← Over.comp_left, GrpObj.one_inv]

theorem sym_pmaps (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := Fin 2) ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]
      D'.sym D.sym (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  refine pmaps_of_section ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (fun k => ?_) _ D'.sym_gen _ D.sym_gen
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (fun y J J' hJ hJ' => ?_)
  · fin_cases k
    · exact inv_hom_fst _ _ hD.e.hom
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have a₁ := val_corr hJ D.sym_rig (specOf φ)
    have a₂ := val_corr hJ' D'.sym_rig (𝟙 _)
    rw [val_pull hJ, val_one] at a₁
    rw [val_pull hJ', val_one, Category.id_comp] at a₂
    rw [hD.he, a₂, Fin.prod_univ_two]
    refine a₁.trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eSec_inv, Category.comp_id]
    simp

theorem even_stalk {T G B Z : Scheme.{0}} {L : LB G} {M : LB B} {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G}
    {iB : B ⟶ B} (w : LB.Iso (L.pull f) (M.pull p))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι)
    (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
    (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
    (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
    (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS) (r : Z ⟶ T) (z : Z) (hz : r z ∈ V) :
    gm r z V (res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1))) =
      gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) * gw w r z (jT 1) (fun _ => jS 1) ∧
    gm r z V (res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))) =
      gw w (r ≫ iT) z (jT 0) (fun _ => jS 0) * gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) :=
  ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₁ hz _).trans (gm_pull r p z _ (h₁ hz) _))
      (gm_res r z h₂ hz _)),
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₃ hz _).trans (gm_pull r iT z ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) (@h₃ (r z) hz) _))
      ((gm_res r z h₄ hz _).trans (gm_pull r f z _ (h₄ hz) _)))⟩

theorem even_of_square {T G B T' G' B' : Scheme.{0}} {L : LB G} {M : LB B} {L' : LB G'} {M' : LB B'}
    (hL : L.IsLB) (hM : M.IsLB)
    {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {f' : T' ⟶ G'} {p' : T' ⟶ B'} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    {Ψ : G' ⟶ G} {Φ : B' ⟶ B} {h : T' ⟶ T}
    (hf : h ≫ f = f' ≫ Ψ) (hp : p' ≫ Φ = h ≫ p) (ih : iT' ≫ h = h ≫ iT)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iF' : iT' ≫ f' = f' ≫ iG') (iP' : iT' ≫ p' = p' ≫ iB')
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p'))
    (wL : LB.Iso L' (L.pull Ψ)) (wM : LB.Iso M' (M.pull Φ))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hs : PMaps wL (K := Fin 2) ![iG', 𝟙 G'] ![iG, 𝟙 G] ![1, -1] s' s Ψ)
    (hσ : PMaps wM (K := Fin 2) ![iB', 𝟙 B'] ![iB, 𝟙 B] ![1, -1] σ' σ Φ)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      Φ (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → Ψ (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL')
    (ev : ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
      ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
        (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
        (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
        (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
        res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1)) =
          res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS)))
    (jS' : Fin 2 → L'.ι) (jT' : Fin 2 → M'.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]).U jT')
    (h₂ : V ≤ (M'.pull p').U (fun _ => jT' 1) ⊓ (L'.pull f').U (fun _ => jS' 1))
    (h₃ : V ≤ iT' ⁻¹ᵁ ((M'.pull p').U (fun _ => jT' 0) ⊓ (L'.pull f').U (fun _ => jS' 0)))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]).U jS') :
    res h₁ (pullU p' _ (σ'.s jT')) * res h₂ (w'.s (fun _ => jT' 1, fun _ => jS' 1)) =
      res h₃ (pullU iT' _ (w'.s (fun _ => jT' 0, fun _ => jS' 0))) * res h₄ (pullU f' _ (s'.s jS')) := by
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := even_stalk w' s' σ' jS' jT' V h₁ h₂ h₃ h₄ (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  choose JL hJL using fun χ : T' ⟶ G => exists_chart hL (χ z)
  choose JM hJM using fun χ : T' ⟶ B => exists_chart hM (χ z)
  obtain ⟨jS, hjS, cS⟩ : ∃ jS : Fin 2 → L.ι, (∀ k, (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) z ∈ L.U (jS k)) ∧
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS :=
    ⟨fun k => JL (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k), fun k => hJL _,
      fun a b e => congrArg (fun q => JL (h ≫ q)) e⟩
  obtain ⟨jT, hjT, cT⟩ : ∃ jT : Fin 2 → M.ι, (∀ k, (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) z ∈ M.U (jT k)) ∧
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT :=
    ⟨fun k => JM (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k), fun k => hJM _,
      fun a b e => congrArg (fun q => JM (h ≫ q)) e⟩
  have S0 : (h ≫ f ≫ iG) z ∈ L.U (jS 0) := hjS 0
  have S1 : (h ≫ f) z ∈ L.U (jS 1) := hjS 1
  have T0 : (h ≫ p ≫ iB) z ∈ M.U (jT 0) := hjT 0
  have T1 : (h ≫ p) z ∈ M.U (jT 1) := hjT 1
  have OrbitIntegralProperties : (h ≫ iT ≫ f) z ∈ L.U (jS 0) := by rw [iF]; exact S0
  have T0a : (h ≫ iT ≫ p) z ∈ M.U (jT 0) := by rw [iP]; exact T0
  have S0b : (iT' ≫ f' ≫ Ψ) z ∈ L.U (jS 0) := by rw [← hf, ← Category.assoc, ih, Category.assoc]; exact OrbitIntegralProperties
  have T0b : (iT' ≫ p' ≫ Φ) z ∈ M.U (jT 0) := by rw [hp, ← Category.assoc, ih, Category.assoc]; exact T0a
  have S0c : ((f' ≫ iG') ≫ Ψ) z ∈ L.U (jS 0) := by rw [← iF', Category.assoc]; exact S0b
  have T0c : ((p' ≫ iB') ≫ Φ) z ∈ M.U (jT 0) := by rw [← iP', Category.assoc]; exact T0b
  have TopsChoiceSecondBound : (f' ≫ Ψ) z ∈ L.U (jS 1) := by rw [← hf]; exact S1
  have T1b : (p' ≫ Φ) z ∈ M.U (jT 1) := by rw [hp]; exact T1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : h z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hjT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0a, mem_pull.2 OrbitIntegralProperties⟩,
    Set.mem_iInter.2 hjS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := even_stalk w s σ jS jT W l₁ l₂ l₃ l₄ h z hW
  have E := n₁.symm.trans ((congrArg (gm h z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  have A₁ := sq _ (𝟙 T') z (jT 1) (jT' 1) (jS 1) (jS' 1) T1b (mem_pull.1 (h₂ hz).1) TopsChoiceSecondBound (mem_pull.1 (h₂ hz).2)
  have A₀ := sq _ iT' z (jT 0) (jT' 0) (jS 0) (jS' 0) T0b (mem_pull.1 (h₃ hz).1) S0b (mem_pull.1 (h₃ hz).2)
  have Bσ := hσ _ p' z jT jT' (Fin.forall_fin_two.2 ⟨T0c, T1b⟩) (Set.mem_iInter.1 (h₁ hz))
  have Bs := hs _ f' z jS jS' (Fin.forall_fin_two.2 ⟨S0c, TopsChoiceSecondBound⟩) (Set.mem_iInter.1 (h₄ hz))
  rw [Fin.prod_univ_two] at Bσ Bs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg] at Bσ Bs
  simp only [Category.id_comp] at A₁ ⊢
  rw [iP', iF', ih] at A₀
  rw [hp] at Bσ
  rw [← hf] at Bs
  apply Additive.ofMul.injective
  have e₁ := congrArg Additive.ofMul E
  have e₂ := congrArg Additive.ofMul A₁
  have e₃ := congrArg Additive.ofMul A₀
  have e₄ := congrArg Additive.ofMul Bσ
  have e₅ := congrArg Additive.ofMul Bs
  simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ ⊢
  linear_combination (norm := abel) e₁ + e₂ - e₃ - e₄ + e₅

end GlobalTheory.EvenPull

namespace GlobalTheory

open GlobalTheory.EvenPull in

theorem pulled_comparison_even : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen → Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' U.symG (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) → ∀ (e : ℕ) (jS : Fin 2 → L'.L.ι) (jT : Fin 2 → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (fstG I' e G').left ≫ (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → _) k) jS → LB.Coh D'.toPre.P.L (fun k => (gt' e).pG.left ≫ (![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] : Fin 2 → _) k) jT → ∀ (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ (gt' e).pG.left ⁻¹ᵁ (LB.LinComb D'.toPre.P.L (K := Fin 2) ![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] ![1, -1]).U jT) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 1) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 1)) (h₃ : V ≤ (ι[thickObj R' I' e G']).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 0) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 0))) (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]).U jS), res h₁ (pullU (gt' e).pG.left _ (D'.toPre.sym.s jT)) * res h₂ ((w' e).s (fun _ => jT 1, fun _ => jS 1)) = res h₃ (pullU (ι[thickObj R' I' e G']).left _ ((w' e).s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU (fstG I' e G').left _ (s'.s jS)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ hbc U L' wL _ _ _ gt' w' _ _ H s' _ hs e jS jT _ _
    V h₁ h₂ h₃ h₄
  obtain ⟨h, hf, ⟨hp, -⟩, sq⟩ := H e
  have iF : ∀ {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G],
      (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    fun I G _ => inv_fst _ G
  have iP : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
      {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G),
      (ι[thickObj R I e G]).left ≫ g.pG.left = g.pG.left ≫ (ι[D.P.A]).left := fun g => by
    have := g.q_hom
    exact inv_hom_fst _ _ g.q
  have : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have m : Mono (fstG I e G).left := pullback.fst_of_mono
  have ih : (ι[thickObj R' I' e G']).left ≫ h = h ≫ (ι[thickObj R I e G]).left := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, Category.assoc, hf, iF, ← Category.assoc, iF,
      Category.assoc, inv_hom_fst _ _ bc.hom, ← Category.assoc h, hf]
    simp only [Category.assoc]
  exact even_of_square U.LG.isLB D.toPre.P.isLB hf hp ih (iF I G) (iP _) (iF I' G') (iP _) (U.w e) (w' e) wL hD.w
    U.symG D.toPre.sym s' D'.toPre.sym hs (sym_pmaps hG hD) sq (U.w_even e) jS jT V h₁ h₂ h₃ h₄

end GlobalTheory
