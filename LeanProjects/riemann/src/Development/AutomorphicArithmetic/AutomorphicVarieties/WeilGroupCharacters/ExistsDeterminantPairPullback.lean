import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.W.FramePullback

section Det

variable {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]

private theorem chi_comap (D : GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp

private theorem lam_comap (D : GDet n A G) (φ : H →* G) (i : ℕ) (y : MonoidAlgebra A H) :
    (D.comap φ).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A φ y) := by
  unfold GDet.lam
  rw [chi_comap]

private theorem tr_zero (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : D.chi 0 = Polynomial.X ^ n := by
    have := D.homog (Polynomial A) Polynomial.X 1
    rw [map_one, mul_one] at this
    rw [← this, GDet.chi, map_zero, sub_zero]
    congr 1
    simp [MonoidAlgebra.one_def]
  unfold GDet.tr GDet.lam
  rw [h1, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private theorem tr_dim_zero (D : GDet 0 A G) (y : MonoidAlgebra A G) : D.tr y = -1 := by
  have h1 : ∀ x, D.D (Polynomial A) x = D.D (Polynomial A) 0 := fun x => by
    have := D.homog (Polynomial A) 0 x
    rw [zero_smul, pow_zero, one_mul] at this
    exact this.symm
  have h2 : D.chi y = 1 := by rw [GDet.chi, h1, ← h1 1, map_one]
  unfold GDet.tr GDet.lam
  rw [h2]
  simp

private theorem ofRep_comap (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

end Det

private theorem adic_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R}
    {f : Γ → R} (hf : AdicCont I f) {φ : Γ' → Γ} (hφ : Continuous φ) : AdicCont I fun x => f (φ x) :=
  fun m => (hf m).comp_continuous hφ

private theorem mu_map {l : ℕ} [Fact l.Prime] {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G →* H) (hφ : Continuous φ) {g : G}
    (hg : g ∈ muG l G) : φ g ∈ muG l H := by
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.1 hg
  refine CommGroup.mem_primaryComponent.2 ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator G).topologicalClosure := (QuotientGroup.eq_one_iff _).1 hk
  have h2 : (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap φ := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage hφ)
    refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
    rw [← Subgroup.map_le_iff_le_comap, commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h3 : φ g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow]; exact h2 h1
  exact (QuotientGroup.eq_one_iff _).2 h3

variable {l : ℕ} [Fact l.Prime] {F' F : GFrame l} (h : FHom F' F)

private theorem continuous_pullback_projection : Continuous h.π₀ := (h.π_cont.comp continuous_subtype_val).subtype_mk _

private theorem pullback_projection_frobenius (v) (g) : h.π₀ (F'.φ v g) = F.φ (h.vl v) (h.gv v g) := Subtype.ext (h.hφ v g).symm

private theorem pullback_projection_conj (g) : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
  apply Subtype.ext
  change h.π (F'.c * g * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
  rw [map_mul, map_mul, map_inv, h.hc]

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R]

private theorem pullback_projection_sign_eq (g) : F.eps O R (h.π₀ g) = F'.eps O R g := by
  change Units.map _ (F.ε (h.π g)) = Units.map _ (F'.ε g)
  rw [h.hε]

private theorem star_single (F : GFrame l) (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp [GFrame.star, GFrame.starOp]

private theorem map_star0 (n : ℕ) (g : F'.G₀) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.star O R n (MonoidAlgebra.single g 1)) =
      F.star O R n (MonoidAlgebra.single (h.π₀ g) 1) := by
  rw [star_single, star_single, pullback_projection_sign_eq, ← pullback_projection_conj, ← map_inv]
  simp

private theorem map_oEl {n : ℕ} (v : F'.Vl) (ψ : Fin n → F.Gv (h.vl v) →* Rˣ) (g : Fin n → F'.Gv v) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.oEl v (fun i => (ψ i).comp (h.gv v)) g) =
      F.oEl (h.vl v) ψ fun i => h.gv v (g i) := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_sub]
  simp [pullback_projection_frobenius]

end UpperTheory.V.W.FramePullback

open UpperTheory.V.W.FramePullback in

theorem UpperTheory.V.W.Pair.isEmpty_of_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R)
    (hn : n = 0) : IsEmpty F.St ∧ IsEmpty F.Vl := by
  subst hn
  refine ⟨⟨fun u => ?_⟩, ⟨fun v => ?_⟩⟩
  · have := p.I u 1 (one_mem _) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)
  · have := p.Ord v (fun _ => 1) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)

open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.exists_determinantPair_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (F' F : GFrame l) (h : FHom F' F) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r' : Resid F' O n) (r : Resid F O n), h.Compat r' r → (n = 0 → IsEmpty F'.St) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R),
      ∃ p' : Pair r' R, p'.D = p.D.comap h.π₀ ∧ ∀ v i, p'.ψ v i = (p.ψ (h.vl v) i).comp (h.gv v) := by
  intro l _ F' F h O _ _ _ n r' r hc hn R _ _ _ p
  have hs : ∀ g : F'.G₀, MonoidAlgebra.mapDomainRingHom R h.π₀ (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (h.π₀ g) 1 := fun g => by simp
  refine ⟨⟨p.D.comap h.π₀, fun v i => (p.ψ (h.vl v) i).comp (h.gv v), fun i => ?_, ?_, fun v i => ⟨?_, fun g => ?_, fun g => ?_⟩,
    fun i g => ?_, fun v g k => ?_, fun u g hg k => ?_⟩, rfl, fun _ _ => rfl⟩
  · simp only [lam_comap, hs]
    exact adic_comp (p.cont i) (continuous_pullback_projection h)
  · have : (p.D.comap h.π₀).map (res O R : R →+* ResidueField O) =
        (p.D.map (res O R : R →+* ResidueField O)).comap h.π₀ := rfl
    rw [this, p.red, Resid.Dbar, ofRep_comap, Resid.Dbar]
    congr 1
    ext g : 1
    have e : r'.chib = fun i => (r.chib i).comp h.π₀ := funext hc.chib
    rw [e]; rfl
  · exact adic_comp (p.psi (h.vl v) i).cont (h.gv_cont v)
  · rw [hc.psib]
    exact (p.psi (h.vl v) i).red _
  · have hg : h.gv v g ∈ F.mu (h.vl v) := mu_map (h.gv v) (h.gv_cont v) g.2
    rw [hc.th v i g hg]
    exact (p.psi (h.vl v) i).mu ⟨_, hg⟩
  · rw [lam_comap, lam_comap, map_star0, hs, p.P]
  · rw [GDet.tr, lam_comap, map_mul, hs, map_oEl]
    exact p.Ord _ _ _
  · rw [GDet.tr, lam_comap, map_mul, map_sub, hs, hs, map_one]
    rcases hc.ip u g hg with h1 | ⟨u', hu'⟩
    · rw [h1, ← MonoidAlgebra.one_def, sub_self, mul_zero]
      exact tr_zero p.D (Nat.pos_of_ne_zero fun h0 => (hn h0).elim u)
    · exact p.I u' _ hu' _
