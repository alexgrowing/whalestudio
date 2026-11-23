import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamPolySmulRight

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

section Mul

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem mulV_mem (X Y Z : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X) (hY : IsDominant Y) (hZ : IsDominant Z)
    (h : ∀ s, lamAt Z s = lamAt X s + lamAt Y s) :
    ∀ F ∈ Vsp Kf X, ∀ r ∈ Vsp Kf Y, F * r ∈ Vsp Kf Z := by
  intro F hF r hr
  unfold Vsp at hF hr ⊢
  refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) F hF r hr
  simp only [if_pos (lamAt_anti X hX s)] at hf
  simp only [if_pos (lamAt_anti Y hY s)] at hg
  simp only [if_pos (lamAt_anti Z hZ s)]
  rw [h s, cbNuOf_add _ _ (lamAt_anti X hX s) (lamAt_anti Y hY s)]
  exact Formalism.GradedWeylDivisibility.dualWeyl_mul hf hg

def mulV (X Y Z : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X) (hY : IsDominant Y) (hZ : IsDominant Z)
    (h : ∀ s, lamAt Z s = lamAt X s + lamAt Y s) : Vsp Kf X →ₗ[Kf] Vsp Kf Y →ₗ[Kf] Vsp Kf Z :=
  LinearMap.mk₂ Kf (fun F r => ⟨F.1 * r.1, mulV_mem X Y Z hX hY hZ h _ F.2 _ r.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem prod_mem_Hten (X : Fin n' → Fin (m + 1) → ℤ) (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (c : Kf)
    (hc : c ≠ 0) (f : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hf : ∀ s, (c ^ (lamAt X s 0)) • f s ∈ H0 O m (lamAt X s) (colSpan O (gs s * lb_D _ 1 c))) :
    (c ^ Ar 1 X) • ∏ s, blockEmb Kf s (f s) ∈ Hten O X (famD O gs c) := by
  have hX : c ^ Ar 1 X = ∏ s, c ^ lamAt X s 0 := by
    rw [Ar_one, Formalism.MainNotions.G.LatticeSystems.lb_zpow_sum c hc]
  rw [hX, ← prod_bE_smul (fun s => c ^ lamAt X s 0) f]
  unfold Hten tensorLat
  exact Submodule.subset_span ⟨fun s => c ^ lamAt X s 0 • f s, hf, rfl⟩

theorem prod_mem_Vsp (X : Fin n' → Fin (m + 1) → ℤ) (hX : IsDominant X)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det)
    (f : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hf : ∀ s, ((1 : Kf) ^ (lamAt X s 0)) • f s ∈ H0 O m (lamAt X s) (colSpan O (gs s * lb_D _ 1 1))) :
    ∏ s, blockEmb Kf s (f s) ∈ Vsp Kf X := by
  have hL : ∀ s, IsLattice O (colSpan O (gs s * lb_D _ 1 (1 : Kf))) :=
    fun s => famD_lat O gs hgs 1 one_ne_zero s
  refine tn_Hten_le X hX (fun s => colSpan O (gs s * lb_D _ 1 (1 : Kf))) hL _ ?_
  unfold Hten tensorLat
  refine Submodule.subset_span ⟨f, fun s => ?_, rfl⟩
  simpa only [one_zpow, one_smul] using hf s

end Mul

theorem cloudTen {p n' : ℕ} (R : RS p n') (m : ℕ) (lam0 H Hp ze lo lo' : Fin n' → Fin (m + 1) → ℤ)
    (dlam : IsDominant lam0) (dH : IsDominant H) (dHp : IsDominant Hp) (dze : IsDominant ze) (dlo : IsDominant lo)
    (dlo' : IsDominant lo') (hadd1 : ∀ s, lamAt Hp s = lamAt H s + lamAt ze s)
    (hadd2 : ∀ s, lamAt lam0 s = lamAt H s + lamAt lo s) (d : Fin n' → ℚ) (κ : Fin n' → ℕ)
    (hpos : ∀ s, PosOK R m (lamAt lam0 s) (lamAt H s) (lamAt Hp s) (lamAt ze s) (lamAt lo s) (lamAt lo' s) (d s) (κ s))
    (hCO : CartanOnto) (hIso : CloudIsoP) :
    ∃ (mH : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf ze →ₗ[R.Kf] Vsp R.Kf Hp)
      (mU : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lo →ₗ[R.Kf] Vsp R.Kf lam0)
      (abelian₂ : Vsp R.Kf lam0 →ₗ[R.Kf] Vsp R.Kf lo' →ₗ[R.Kf] Vsp R.Kf Hp),
      (∀ M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV ze (Hten R.O ze M), mH F z ∈ toV Hp (Hten R.O Hp M)) ∧
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV lo (Hten R.O lo M), mU F z ∈ toV lam0 (Hten R.O lam0 M)) ∧
        (∀ v ∈ toV lam0 (Hten R.O lam0 M), ∀ z ∈ toV lo' (Hten R.O lo' M), abelian₂ v z ∈ toV Hp (Hten R.O Hp M))) ∧
      ∀ gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (gs s).det) →
        ∃ (nb : ℕ) (z0 : Vsp R.Kf ze) (s : Fin nb → Vsp R.Kf lo) (s' : Fin nb → Vsp R.Kf lo') (ka : Fin nb → ℕ),
          (nb : ℚ) = ∏ s, d s ∧ (∀ b, ka b ≤ ∑ s, κ s) ∧
          (∀ a' b F, abelian₂ (mU F (s b)) (s' a') = if a' = b then ((p : R.Kf) ^ ka b) • mH F z0 else 0) ∧
          ∀ c : R.Kf, c ≠ 0 →
            (c ^ Ar 1 ze) • z0 ∈ toV ze (Hten R.O ze (famD R.O gs c)) ∧
            (∀ b, (c ^ Ar 1 lo) • s b ∈ toV lo (Hten R.O lo (famD R.O gs c))) ∧
            (∀ a', (c ^ Ar 1 lo') • s' a' ∈ toV lo' (Hten R.O lo' (famD R.O gs c))) ∧
            (∀ F, mH F ((c ^ Ar 1 ze) • z0) ∈ toV Hp (Hten R.O Hp (famD R.O gs c)) →
              F ∈ toV H (Hten R.O H (famD R.O gs c))) := by
  classical
  haveI : IsFractionRing R.O R.Kf := R.std.1.frac_O
  have hw : Irreducible R.w := R.std.2.1
  have hH0 : ∀ (a b : Fin (m + 1) → ℤ), Antitone a → Antitone b →
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
        ∀ F ∈ H0 R.O m a Λ, ∀ G ∈ H0 R.O m b Λ, F * G ∈ H0 R.O m (a + b) Λ := by
    intro a b ha hb Λ hΛ F hF G hG
    rw [hCO R.O R.Kf m a b Λ hΛ ha hb]
    exact Submodule.subset_span ⟨F, hF, G, hG, rfl⟩
  unfold PosOK at hpos
  choose Ls hA hB hC using hpos
  obtain ⟨T, hT⟩ := KP.tensorMap (K := R.Kf) (S := Fin n')
    (fun s => (blockEmb R.Kf s).toLinearMap ∘ₗ Ls s)
  have hT' : ∀ Q : Fin n' → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      T (∏ s, rename (fun x => (s, x)) (Q s)) = ∏ s, blockEmb R.Kf s (Ls s (Q s)) := fun Q => hT Q
  have hLV : ∀ V ∈ Vsp R.Kf lam0, ∀ W ∈ Vsp R.Kf lo', lamPoly T V W ∈ Vsp R.Kf Hp := by
    unfold Vsp
    refine lamPoly_mem T Ls hT' _ _ _ (fun s v hv t ht => ?_)
    simp only [if_pos (lamAt_anti lam0 dlam s)] at hv
    simp only [if_pos (lamAt_anti lo' dlo' s)] at ht
    simp only [if_pos (lamAt_anti Hp dHp s)]
    exact hA s v hv t ht
  refine ⟨mulV H ze Hp dH dze dHp hadd1, mulV H lo lam0 dH dlo dlam hadd2,
    LinearMap.mk₂ R.Kf (fun V W => (⟨lamPoly T V.1 W.1, hLV _ V.2 _ W.2⟩ : Vsp R.Kf Hp))
      (fun a b c => Subtype.ext (lamPoly_add_left T _ _ _))
      (fun c a b => Subtype.ext (lamPoly_smul_left T c _ _))
      (fun a b c => Subtype.ext (lamPoly_add_right T _ _ _))
      (fun c a b => Subtype.ext (lamPoly_smul_right T c _ _)), ?_, ?_⟩
  · intro M hM
    refine ⟨fun F hF z hz => ?_, fun F hF z hz => ?_, fun v hv z hz => ?_⟩
    · have hF' : F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (M s)) := hF
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt ze s) (M s)) := hz
      show F.1 * z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (M s))
      refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) _ hF' _ hz'
      rw [hadd1 s]
      exact hH0 _ _ (lamAt_anti H dH s) (lamAt_anti ze dze s) (M s) (hM s) f hf g hg
    · have hF' : F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (M s)) := hF
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lo s) (M s)) := hz
      show F.1 * z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lam0 s) (M s))
      refine tensorLat_mul _ _ _ (fun s f hf g hg => ?_) _ hF' _ hz'
      rw [hadd2 s]
      exact hH0 _ _ (lamAt_anti H dH s) (lamAt_anti lo dlo s) (M s) (hM s) f hf g hg
    · have hv' : v.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lam0 s) (M s)) := hv
      have hz' : z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt lo' s) (M s)) := hz
      show lamPoly T v.1 z.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (M s))
      exact lamPoly_mem T Ls hT' _ _ _ (fun s v' hv'' t ht => hB s (M s) (hM s) v' hv'' t ht) _ hv' _ hz'
  · intro gs hgs
    choose nb z0 sv sv' ka hnb hka hmul hcc using fun s => hC s (gs s) (hgs s)
    let e : Fin (∏ s, nb s) ≃ ((s : Fin n') → Fin (nb s)) := finPiFinEquiv.symm
    have key : ∀ f ∈ Vsp R.Kf H, ∀ a' b : Fin (∏ s, nb s),
        lamPoly T (f * ∏ s, blockEmb R.Kf s (sv s (e b s))) (∏ s, blockEmb R.Kf s (sv' s (e a' s))) =
          if a' = b then ((p : R.Kf) ^ (∑ s, ka s (e b s))) • (f * ∏ s, blockEmb R.Kf s (z0 s)) else 0 := by
      intro f hf a' b
      unfold Vsp tensorLat at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨G, hG, rfl⟩ := hx
        have hGs : ∀ s, G s ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) := fun s => by
          have h := hG s
          simp only [if_pos (lamAt_anti H dH s)] at h
          exact h
        rw [show (∏ s, blockEmb R.Kf s (G s)) * ∏ s, blockEmb R.Kf s (sv s (e b s)) =
            ∏ s, blockEmb R.Kf s (G s * sv s (e b s)) by
          rw [← Finset.prod_mul_distrib]; simp only [map_mul]]
        rw [lamPoly_prod T Ls hT']
        by_cases hab : a' = b
        · subst hab
          have hfac : ∀ s, Ls s (blockEmb R.Kf true (G s * sv s (e a' s)) * blockEmb R.Kf false (sv' s (e a' s))) =
              ((p : R.Kf) ^ ka s (e a' s)) • (z0 s * G s) := fun s => by
            rw [hmul s _ _ _ (hGs s), if_pos rfl]
          rw [if_pos rfl]
          simp only [hfac]
          rw [prod_bE_smul, Finset.prod_pow_eq_pow_sum]
          congr 1
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun s _ => by rw [map_mul, mul_comm]
        · rw [if_neg hab]
          have hex : ∃ s, e a' s ≠ e b s := by
            by_contra hcon
            push_neg at hcon
            exact hab (e.injective (funext hcon))
          obtain ⟨s0, hs0⟩ := hex
          apply Finset.prod_eq_zero (Finset.mem_univ s0)
          rw [hmul s0 _ _ _ (hGs s0), if_neg hs0, map_zero]
      | zero => simp only [zero_mul, lamPoly_zero_left, smul_zero, ite_self]
      | add x y _ _ hx hy =>
        rw [add_mul, lamPoly_add_left, hx, hy]
        split_ifs
        · rw [add_mul, smul_add]
        · rw [add_zero]
      | smul c x _ hx =>
        rw [smul_mul_assoc, lamPoly_smul_left, hx]
        split_ifs
        · rw [smul_mul_assoc, smul_comm]
        · rw [smul_zero]
    refine ⟨∏ s, nb s,
      ⟨∏ s, blockEmb R.Kf s (z0 s), prod_mem_Vsp ze dze gs hgs z0 (fun s => (hcc s 1 one_ne_zero).1)⟩,
      fun b => ⟨∏ s, blockEmb R.Kf s (sv s (e b s)),
        prod_mem_Vsp lo dlo gs hgs _ (fun s => (hcc s 1 one_ne_zero).2.2.1 (e b s))⟩,
      fun a' => ⟨∏ s, blockEmb R.Kf s (sv' s (e a' s)),
        prod_mem_Vsp lo' dlo' gs hgs _ (fun s => (hcc s 1 one_ne_zero).2.2.2 (e a' s))⟩,
      fun b => ∑ s, ka s (e b s), ?_, ?_, ?_, ?_⟩
    · rw [Nat.cast_prod]
      exact Finset.prod_congr rfl fun s _ => hnb s
    · intro b
      exact Finset.sum_le_sum fun s _ => hka s _
    · intro a' b F
      obtain ⟨f, hf⟩ := F
      have hk := key f hf a' b
      split_ifs at hk ⊢ with hab
      · exact Subtype.ext hk
      · exact Subtype.ext hk
    · intro c hc
      refine ⟨?_, fun b => ?_, fun a' => ?_, fun F hF => ?_⟩
      · show (c ^ Ar 1 ze) • (∏ s, blockEmb R.Kf s (z0 s)) ∈ Hten R.O ze (famD R.O gs c)
        exact prod_mem_Hten ze gs c hc z0 (fun s => (hcc s c hc).1)
      · show (c ^ Ar 1 lo) • (∏ s, blockEmb R.Kf s (sv s (e b s))) ∈ Hten R.O lo (famD R.O gs c)
        exact prod_mem_Hten lo gs c hc _ (fun s => (hcc s c hc).2.2.1 (e b s))
      · show (c ^ Ar 1 lo') • (∏ s, blockEmb R.Kf s (sv' s (e a' s))) ∈ Hten R.O lo' (famD R.O gs c)
        exact prod_mem_Hten lo' gs c hc _ (fun s => (hcc s c hc).2.2.2 (e a' s))
      · show F.1 ∈ tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt H s) (famD R.O gs c s))
        have hF' : F.1 * ((c ^ Ar 1 ze) • ∏ s, blockEmb R.Kf s (z0 s)) ∈
            tensorLat R.O R.Kf (fun s => H0 R.O m (lamAt Hp s) (famD R.O gs c s)) := hF
        rw [Ar_one, ← Formalism.MainNotions.G.LatticeSystems.lb_zpow_sum c hc, ← prod_bE_smul, mul_comm] at hF'
        simp only [hadd1] at hF'
        have h2 : F.1 ∈ tensorLat R.Kf R.Kf
            (fun s => if Antitone (lamAt H s) then dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) else ⊥) := F.2
        have hfun : (fun s => if Antitone (lamAt H s) then dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) else ⊥) =
            fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt H s)) :=
          funext fun s => if_pos (lamAt_anti H dH s)
        rw [hfun] at h2
        exact hIso R.O R.Kf R.w hw n' m (fun s => lamAt H s) (fun s => lamAt ze s) (lamAt_anti H dH)
          (lamAt_anti ze dze) (famD R.O gs c) (fun s => famD_lat R.O gs hgs c hc s)
          (fun s => c ^ lamAt ze s 0 • z0 s) (fun s => (hcc s c hc).1) (fun s => (hcc s c hc).2.1) F.1 h2 hF'

end Formalism.MainNotions.flipOneThree.Pf

end
