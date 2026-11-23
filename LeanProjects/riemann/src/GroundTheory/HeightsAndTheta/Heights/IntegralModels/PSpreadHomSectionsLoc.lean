import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSectionsLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsZLocDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullInjLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace SpreadHomSectionsLoc

lemma map_eqToHom_symm (Z : Scheme.{0}) {A B : Z.Opens} (h : A = B) (x : Γ(Z, A)) :
    (Z.presheaf.map (eqToHom h).op).hom ((Z.presheaf.map (eqToHom h.symm).op).hom x) = x := by
  subst h
  simp

lemma exists_app_restrict_eq_nsmul (h₁ : ZLocDenominators.Statement) {X : Scheme.{0}}
    (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens) (V : (U : Scheme.{0}).Opens) (hV : IsAffineOpen V)
    (b : Γ((baseChangeMap f (ZLoc p) ⁻¹ᵁ U : Scheme.{0}), (baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)) :
    ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ((U : Scheme.{0}), V),
      (baseChangeMap f (ZLoc p) ∣_ U).app V c = N • b := by
  have e := image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) U V
  obtain ⟨N, hN, hpN, c, hc⟩ := h₁ X f p (U.ι ''ᵁ V) (hV.image_of_isOpenImmersion U.ι)
    (((baseChange f (ZLoc p)).presheaf.map (eqToHom e.symm).op).hom b)
  refine ⟨N, hN, hpN, c, ?_⟩
  rw [morphismRestrict_app]
  change ((baseChange f (ZLoc p)).presheaf.map (eqToHom e).op).hom
    ((baseChangeMap f (ZLoc p)).app _ c) = N • b
  rw [hc, map_nsmul]
  congr 1
  exact map_eqToHom_symm _ e b

variable {Y T : Scheme.{0}} (π : T ⟶ Y) (p : ℕ)

lemma exists_pull_eq_nsmul (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {G : Y.Modules} {k : ℕ} {e : Fin k → Γ(G, W)} (he : IsBasisOn G W e)
    (σ : Γ((Scheme.Modules.pullback π).obj G, π ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ τ : Γ(G, W), pullSectionOn π G W τ = N • σ := by
  have hb := (h₂ _ _ π G W k e he).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN hpN c hc using fun i => hden (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun h => ?_,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • c i) • e i, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 h
    exact hpN i hi
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, hc i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]

lemma exists_pull_eq_nsmul_hom (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, W)} {e' : Fin k' → Γ(G, W)}
    (he : IsBasisOn F W e) (he' : IsBasisOn G W e') :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∀ V : Y.Opens, V ≤ W → ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
      pullSectionOn π G V τ = N • φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
  classical
  choose N hN hpN τ hτ using fun i => exists_pull_eq_nsmul π p hp h₂ hden he'
    (φ.app _ (pullSectionOn π F _ (e i)))
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun h => ?_, fun V hV s => ?_⟩
  · obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 h
    exact hpN i hi
  obtain ⟨r, rfl⟩ := (he V hV).2 s
  refine ⟨∑ i, r i • (G.presheaf.map (homOfLE hV).op).hom ((∏ j ∈ Finset.univ.erase i, N j) • τ i), ?_⟩
  have hV' : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ W := (Opens.map π.base).monotone hV
  rw [pullSectionOn_sum, pullSectionOn_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, smul_comm]
  congr 1
  rw [pullSectionOn_res _ _ hV (homOfLE hV'), pullSectionOn_res _ _ hV (homOfLE hV'), map_nsmul, hτ,
    smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), app_map_apply, map_nsmul]

theorem main (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) (fY : Y ⟶ SpecZ) [CompactSpace Y]
    (hden : ∀ W : Y.Opens, IsAffineOpen W → ∀ b : Γ(T, π ⁻¹ᵁ W),
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (hF : IsVectorBundle F) (hG : IsVectorBundle G)
    (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hpm₀ : ¬ p ∣ m₀)
    (hinj : ∀ n : ℕ, 0 < n → m₀ ∣ n → ¬ p ∣ n → ∀ V : Y.Opens, V ≤ invOpen fY n →
      Function.Injective (pullSectionOn π G V)) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ p ∣ n →
      ∀ V : Y.Opens, V ≤ invOpen fY n → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
        pullSectionOn π G V t = φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
  classical

  have chart : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧
      ∀ V : Y.Opens, V ≤ W → ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
        pullSectionOn π G V τ = N • φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
    intro y
    obtain ⟨U₁, -, hy₁, k, e, he⟩ := hF y
    obtain ⟨U₂, -, hy₂, k', e', he'⟩ := hG y
    obtain ⟨W, hW, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ U₁ ⊓ U₂ from ⟨hy₁, hy₂⟩)
    obtain ⟨N, hN, hpN, hτ⟩ := exists_pull_eq_nsmul_hom π p hp h₂ (hden W hW) φ
      (he.restrict (hWle.trans inf_le_left)) (he'.restrict (hWle.trans inf_le_right))
    exact ⟨W, hW, hyW, N, hN, hpN, hτ⟩
  choose W hW hyW N hN hpN hτ using chart

  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  have hcov : ∀ x : Y, ∃ y : S, x ∈ W y := by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hx⟩
  refine ⟨m₀ * ∏ y ∈ S, N y, Nat.mul_pos hm₀ (Finset.prod_pos fun y _ => hN y), ?_,
    fun n hn hmn hpn V hV s => ?_⟩
  · rw [(Nat.Prime.prime hp).dvd_mul, (Nat.Prime.prime hp).dvd_finsetProd_iff]
    rintro (h | ⟨y, -, hy⟩)
    exacts [hpm₀ h, hpN y hy]
  have hinjV := hinj n hn (dvd_trans (dvd_mul_right _ _) hmn) hpn

  have loc : ∀ y : S, ∃ t : Γ(G, V ⊓ W y),
      pullSectionOn π G _ t = (((Scheme.Modules.pullback π).obj G).presheaf.map
        (homOfLE ((Opens.map π.base).monotone (inf_le_left : V ⊓ W y ≤ V))).op).hom
          (φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s)) := by
    intro y
    obtain ⟨τ, hτy⟩ := hτ y (V ⊓ W y) inf_le_right
      ((F.presheaf.map (homOfLE (inf_le_left : V ⊓ W y ≤ V)).op).hom s)
    have hu : IsUnit ((N y : ℕ) : Γ(Y, V ⊓ W y)) := by
      have h1 := isUnit_intCast_of_le_invOpen fY (n : ℤ) (V := V ⊓ W y) (inf_le_left.trans hV)
      obtain ⟨c, hc⟩ := (Finset.dvd_prod_of_mem N y.2).trans ((dvd_mul_left _ _).trans hmn)
      rw [hc] at h1
      push_cast at h1
      exact isUnit_of_mul_isUnit_left h1
    refine ⟨(hu.unit⁻¹).val • τ, ?_⟩
    rw [pullSectionOn_smul, hτy, ← Nat.cast_smul_eq_nsmul (R := Γ(T, π ⁻¹ᵁ (V ⊓ W y))), smul_smul,
      ← map_natCast (π.app (V ⊓ W y)).hom, ← map_mul, IsUnit.val_inv_mul, map_one, one_smul,
      pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)),
      app_map_apply]
  choose t ht using loc

  obtain ⟨t', ht'⟩ := modules_exists_glue G (V := V) (fun y : S => V ⊓ W y)
    (fun _ => inf_le_left) (fun x _ => by obtain ⟨y, hy⟩ := hcov x; exact ⟨y, ‹_›, hy⟩) t
    (fun y z => by
      apply hinjV _ (inf_le_left.trans (inf_le_left.trans hV))
      rw [pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)),
        pullSectionOn_res _ _ inf_le_right (homOfLE ((Opens.map π.base).monotone inf_le_right)),
        ht, ht, res_res _ _ _ (homOfLE ((Opens.map π.base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ W y ⊓ (V ⊓ W z) ≤ V))),
        res_res _ _ _ (homOfLE ((Opens.map π.base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ W y ⊓ (V ⊓ W z) ≤ V)))])
  refine ⟨t', ?_⟩
  apply modules_eq_of_locally
  intro z hz
  obtain ⟨y, hy⟩ := hcov (π.base z)
  refine ⟨π ⁻¹ᵁ (V ⊓ W y), (Opens.map _).monotone inf_le_left, ⟨hz, hy⟩, ?_⟩
  rw [← pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)), ht', ht]

end SpreadHomSectionsLoc

theorem SpreadHomSectionsLoc.proof (h₁ : ZLocDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    (h₃ : PullInjLoc.Statement) : SpreadHomSectionsLoc.Statement := by
  intro X f _ _ p U F G hF hG φ
  obtain ⟨m₀, hm₀, hpm₀, hinj⟩ := h₃ X f p U G hG
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  have : CompactSpace (U : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set X))
  exact SpreadHomSectionsLoc.main _ _ p.2 h₂ (U.ι ≫ f)
    (fun W hW b => SpreadHomSectionsLoc.exists_app_restrict_eq_nsmul h₁ f p U W hW b) hF hG φ hm₀ hpm₀ hinj

end

end GroundTheory.Heights₂.Heights.Model
