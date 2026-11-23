import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.CyclicQuot

theorem match_of_coprime {A K ι : Type} [CommRing A] [CommRing K] (p : A →+* K) (H : AddSubgroup (ι → A))
    (T k : ℤ) (hc : IsCoprime k T) (y z : ι → A) (hy : T • y ∈ H) (hz : z ∈ H)
    (h : ∀ b, p (z b) = (k : K) * p (y b)) : ∃ z' ∈ H, ∀ b, p (z' b) = p (y b) := by
  obtain ⟨u, w, huw⟩ := hc
  refine ⟨u • z + w • (T • y), H.add_mem (H.zsmul_mem hz u) (H.zsmul_mem hy w), fun b => ?_⟩
  have h' : (u : K) * k + w * T = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huw
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_zsmul, h b]
  simp only [zsmul_eq_mul]
  linear_combination (p (y b)) * h'

theorem coprime_sub {T : ℕ} (hT : T.Prime) (i j : Fin T) (hij : i ≠ j) :
    IsCoprime (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) (T : ℤ) := by
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  refine (hp.irreducible.coprime_iff_not_dvd.mpr fun hd => hij ?_).symm
  have hi := i.2
  have hj := j.2
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  exact Fin.ext (by omega)

theorem cyclic_of_components {A K ι : Type} [CommRing A] [CommRing K] (sp : A ≃+* K × K) (O : Subring A)
    (e : A) (he : e ∈ O) (hsp : sp e = (1, 0)) (M D : Submodule O (ι → A)) (T : ℕ) (hT : T.Prime)
    (hTD : ∀ y ∈ D, (T : ℤ) • y ∈ M)
    (y₁ : ι → A) (hy₁ : y₁ ∈ D) (h₁ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).1 = (sp (y₁ b)).1)
    (y₂ : ι → A) (hy₂ : y₂ ∈ D) (h₂ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).2 = (sp (y₂ b)).2)
    (hidx : M.toAddSubgroup.relIndex D.toAddSubgroup = T ^ 2) :
    ∃ d ∈ D, ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ M := by
  classical
  let eO : O := ⟨e, he⟩
  let d : ι → A := eO • y₁ + (1 - eO) • y₂
  have hd : d ∈ D := D.add_mem (D.smul_mem _ hy₁) (D.smul_mem _ hy₂)
  have hdb : ∀ b, sp (d b) = ((sp (y₁ b)).1, (sp (y₂ b)).2) := by
    intro b
    have : d b = e * y₁ b + (1 - e) * y₂ b := rfl
    rw [this, map_add, map_mul, map_mul, map_sub, map_one, hsp]
    ext <;> simp
  let a : Fin T × Fin T → O := fun ij => ((ij.1 : ℕ) : O) * eO + ((ij.2 : ℕ) : O) * (1 - eO)
  have ha : ∀ ij, sp (a ij : A) = (((ij.1 : ℕ) : K), ((ij.2 : ℕ) : K)) := by
    intro ij
    have : (a ij : A) = ((ij.1 : ℕ) : A) * e + ((ij.2 : ℕ) : A) * (1 - e) := by
      simp [a, eO]
    rw [this, map_add, map_mul, map_mul, map_sub, map_one, hsp, map_natCast, map_natCast]
    ext <;> simp
  let φ : Fin T × Fin T → D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup :=
    fun ij => QuotientAddGroup.mk ⟨a ij • d, D.smul_mem _ hd⟩
  have hcard : Nat.card (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) = T ^ 2 := hidx
  have hfin : Finite (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hT.ne_zero)
  have hinj : Function.Injective φ := by
    intro s t hst
    have hm : -(a s • d) + a t • d ∈ M := QuotientAddGroup.eq.mp hst
    have hc : ∀ b, sp ((-(a s • d) + a t • d) b) =
        ((((t.1 : ℕ) : K) - ((s.1 : ℕ) : K)) * (sp (y₁ b)).1,
          (((t.2 : ℕ) : K) - ((s.2 : ℕ) : K)) * (sp (y₂ b)).2) := by
      intro b
      have : (-(a s • d) + a t • d) b = -((a s : A) * d b) + (a t : A) * d b := rfl
      rw [this, map_add, map_neg, map_mul, map_mul, ha, ha, hdb]
      ext <;> simp <;> ring
    by_contra hne
    by_cases h1 : t.1 = s.1
    · have h2 : t.2 ≠ s.2 := fun h2 => hne (Prod.ext h1.symm h2.symm)
      refine h₂ (match_of_coprime ((RingHom.snd K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h2) y₂ _ (hTD _ hy₂) hm fun b => ?_)
      have := congrArg Prod.snd (hc b)
      push_cast
      exact this
    · refine h₁ (match_of_coprime ((RingHom.fst K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h1) y₁ _ (hTD _ hy₁) hm fun b => ?_)
      have := congrArg Prod.fst (hc b)
      push_cast
      exact this
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard]; simp [sq])
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (QuotientAddGroup.mk ⟨x, hx⟩)
  have hm : -(a s • d) + x ∈ M := QuotientAddGroup.eq.mp hs
  refine ⟨a s, (a s).2, ?_⟩
  rw [sub_eq_neg_add]
  exact hm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem [StarRing E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ e ∈ intV E v, sp e = (1, 0) := by
  have hH : IsHerm (cm.sig : E →+* E) (1 : Matrix (Fin 1) (Fin 1) E) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [cT]
  let L : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hL : ∀ x ∈ L, ∀ b, x b ∈ intOE E := by
    intro x hx b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨c, by simp [Algebra.smul_def]⟩
  have hloc : ∀ y ∈ loc v L, ∀ b, y b ∈ intV E v := by
    intro y hy b
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Subring.subset_closure (Or.inl ⟨⟨x b, hL x hx b⟩, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem c.2 hx
  have hone : (fun _ => 1 : Fin 1 → E ⊗[F] v.adicCompletion F) ∈ loc v L :=
    Submodule.subset_span ⟨fun _ => 1, Submodule.subset_span rfl, by funext i; simp⟩
  have hmem := ((GlobalTheory.T.split_place_lattice_components F E cm 1 1 hH (by simp) v sp h1 h2).1 L (fun _ => sp.symm (1, 0))).mpr
    ⟨⟨_, hone, fun b => by simp⟩, ⟨0, zero_mem _, fun b => by simp⟩⟩
  exact ⟨sp.symm (1, 0), hloc _ hmem 0, by simp⟩

theorem smul_mem_loc {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) : ∀ y ∈ loc v (dualL σ J L), (T : ℤ) • y ∈ loc v L := by
  have h0 : ∀ x ∈ dualL σ J L, (T : ℤ) • x ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have := h x hx
      rwa [Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact L.smul_mem c hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h0 x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_zsmul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem local_dual_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 → ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL v hv sp h1 h2 hiff hidx
  obtain ⟨e, he, hsp⟩ := exists_idem cm v sp h1 h2
  obtain ⟨x, hx, hxn⟩ := hL.2.2.2.2 v hv
  have crit := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp h1 h2).1 L x
  have n1 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1 :=
    fun h => hxn (crit.mpr ⟨h x hx, hiff.mp h x hx⟩)
  have n2 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2 :=
    fun h => n1 (hiff.mpr h)
  obtain ⟨y₁, hy₁⟩ := not_forall.mp n1
  obtain ⟨y₂, hy₂⟩ := not_forall.mp n2
  obtain ⟨hy₁, h₁⟩ := Classical.not_imp.mp hy₁
  obtain ⟨hy₂, h₂⟩ := Classical.not_imp.mp hy₂
  exact cyclic_of_components sp (intV E v) e he hsp _ _ T hT
    (smul_mem_loc cm.sig J T L hL.2.2.1 v) y₁ hy₁ h₁ y₂ hy₂ h₂ hidx

end GlobalTheory.St.G.CyclicQuot

end
