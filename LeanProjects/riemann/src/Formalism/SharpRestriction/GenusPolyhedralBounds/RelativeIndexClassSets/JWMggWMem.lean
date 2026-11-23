import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GeneratorsLeRestrictedSpan
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsIrreducibleLocToCompl
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IteratedWeightAtVanishingOrder
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsCoeffOfMemSpan
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VEtNonnegOfTied

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem upO_Msup_le {X : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j) :
    upO X la N (X.Msup ka) ≤ (Vw X la N ka).restrictScalars (Op X la N) := by
  rw [upO, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨F, -, rfl⟩ := hy
  exact Submodule.subset_span ⟨F, rfl⟩

section

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

theorem jW_MggW_mem (S : Scal B) (CRm c : ℝ)
    (hΘM : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (x : ↥(T0.WL X (addL wF wL T) la)) (hx : x ∈ MggW X la (addL wF wL T) CRm T c) :
    jW X la G.N (addL wF wL T) x ∈ NovK G la := by
  have hle : X.emb (addL wF wL T) (MggO B CRm T c j (addL wF wL T)) ≤ X.Msup (addL wF wL T) :=
    T0.emb_mono X _ inf_le_left
  have h1 : jW X la G.N (addL wF wL T) x ∈ Submodule.span (Op X la G.N) (jW X la G.N (addL wF wL T) ''
      (MggW X la (addL wF wL T) CRm T c : Set ↥(T0.WL X (addL wF wL T) la))) := Submodule.subset_span ⟨x, hx, rfl⟩
  unfold MggW at h1
  rw [span_jW_inW X la G.N _ _ hle] at h1
  have h2 : Submodule.span (Op X la G.N) {f : ↥(Vw X la G.N (addL wF wL T)) |
      ∃ F ∈ X.emb (addL wF wL T) (MggO B CRm T c j (addL wF wL T)), (f : Rp X la G.N) = emb X la G.N F} ≤
      (NovK G la).restrictScalars (Op X la G.N) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨_, ⟨F, hF, rfl⟩, hf⟩
    show f ∈ NovK G la
    rw [NovK_eq, ZK, ← Submodule.span_union, mem_span_subtype_iff (R := Kp X la G.N) (Vw X la G.N (addL wF wL T))]
    have h3 : (f : Rp X la G.N) ∈ Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) :=
      Submodule.subset_span ⟨F, hF.2, hf.symm⟩
    refine Submodule.span_mono ?_ (hCM h3)
    rintro v (⟨al, i, hal', rfl⟩ | ⟨k, rfl⟩)
    · have hle' : ∑ i, al i ≤ T := le_trans hal'.le (Nat.sub_le _ _)
      have hm := upO_Msup_le la G.N (addL wF wL T) (upO_mono la G.N hΘM (upO_mono la G.N (le_sup_of_le_left le_sup_left)
        (secPow_mul_mem_upO la G.w hw al hle' (A := X.emb wF (X.Thc S.sF wF)) ⟨G.th' i, hth' i, rfl⟩)))
      exact ⟨⟨_, hm⟩, Or.inl ⟨al, i, hal', rfl⟩, rfl⟩
    · have h := secPow_mul_mem_upO la G.w hw (G.alz k) (n := a0 D j T) (hal k).le
        (A := X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF))) ⟨G.th0 k, hth0 k, rfl⟩
      rw [hal k, Nat.sub_self, pow_zero, mul_one] at h
      have hm := upO_Msup_le la G.N (addL wF wL T) (upO_mono la G.N hΘM
        (upO_mono la G.N (le_sup_of_le_left le_sup_right) h))
      exact ⟨⟨_, hm⟩, Or.inr ⟨k, rfl⟩, rfl⟩
  exact h2 h1

theorem localIdx (Q : LocalPointData G la) (S : Scal B) (CRm c : ℝ) (e : ℕ) (νs cp : ℝ) (v : PtsG G la → ℝ) [Fintype (PtsG G la)]
    (hM : Submodule.IsLattice B.KO (B.Mlat j (addL wF wL T)))
    (hΘM : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hspK : Submodule.span B.KO (X.Thc S.sK (addL wF wL T) : Set (B.Cusp j (addL wF wL T))) = ⊤)
    (hT1 : 1 ≤ T) (hDT : WeightFamilies.dimY D j ≤ T)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hwM : ∀ k, G.w k ∈ B.Mlat j wL)
    (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF) (hth'M : ∀ i, G.th' i ∈ B.Mlat j wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hth0M : ∀ k, G.th0 k ∈ B.Mlat j (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hzc : ∀ k β, X.inc _ (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β)
    (hdet : ∃ φ : Fin G.rz → B.Cusp j (addL wF wL T) →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)
    (hthK : ∀ i, ((G.th i : B.Mlat j (addL wF wL T)) : B.Cusp j (addL wF wL T)) ∈ X.Thc S.sK (addL wF wL T))
    (hsp : Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j (addL wF wL T)) : B.Cusp j (addL wF wL T))) ⊔
      WeightFamilies.MggK B CRm T c j (addL wF wL T) = ⊤)
    (hB : InBasis G la) (hC : Q.InCurve) (hTie : Q.InTie S)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (hcp : 0 ≤ cp) (hv : ∀ ζ, 0 ≤ v ζ) (hν : ∀ ζ, Q.nu S ζ ≤ νs + cp * v ζ) (he : (T : ℝ) * νs ≤ (e : ℝ))
    (hLB : Module.length (Op X la G.N) (↥(Q.AA T) ⧸ (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * Q.Ila.toNat : ℕ) : ℕ∞))
    (hLP : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞))
    (U : Submodule (X.Kl la) ↥(T0.WL X (addL wF wL T) la)) :
    (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(T0.WL X (addL wF wL T) la) (T0.MW X (addL wF wL T) la ⊓ U.restrictScalars (X.Ol la))
              (T0.ThW X S (addL wF wL T) wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤
      (e : ℝ) * (finrank (X.Kl la) U : ℝ) +
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) *
          ((T : ℝ) * cp * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * v ζ) +
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (Q.Ila.toNat : ℝ) +
        (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j (addL wF wL T)) G.zc la : ℝ) +
        ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j (addL wF wL T) ⧸ Submodule.span (𝓞 B.KO)
          (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j (addL wF wL T))))).toNat : ℝ) := by
  have hLat := inLat_of X S (addL wF wL T) wL wF T la hM hΘM hspK
  have : FiniteDimensional (X.Kl la) ↥(T0.WL X (addL wF wL T) la) := T0.finDim_of_isLat _ hLat.1
  have hN1 := generators_le_thetaSpan G la S hΘM hw hth'
  have hZ1 := zeroGenerators_le_thetaSpan G la S hΘM hw hth0 hal
  have hTM := thetaSpan_le_integralForms G la S hΘM
  have hZlen := len_Zm_le G la hM.fg hDT hwM hth0M hal hzc hdet
  have hqne := quot_len_ne_top la (addL wF wL T) CRm T c G.th hM hsp
  have hLP' : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ ζ, (max 0 ⌈(ep (unifO X la G.N) ζ : ℝ) *
        ((T : ℝ) * Q.nu S ζ - (e : ℝ))⌉).toNat * fdeg ζ : ℕ) : ℕ∞) := by
    rw [finsum_eq_sum_of_fintype] at hLP
    exact hLP
  have hthΘ : ∀ i, toW X la (addL wF wL T) (G.th i) ∈ T0.ThW X S (addL wF wL T) wL wF T la := fun i => by
    show X.bc la (X.inc (addL wF wL T) (G.th i)) ∈ X.loc la (X.Theta S (addL wF wL T) wL wF T)
    exact Submodule.subset_span ⟨X.inc (addL wF wL T) (G.th i),
      (show X.emb _ (X.Thc S.sK (addL wF wL T)) ≤ X.Theta S (addL wF wL T) wL wF T from le_sup_right)
        ⟨_, hthK i, rfl⟩, rfl⟩
  have key := levelsQDesc (PtsG G la) (ep (unifO X la G.N)) fdeg (Q.nu S) v νs cp T
    (Nat.choose (T - 1) (WeightFamilies.dimY D j)) Q.Ila.toNat (fun ζ => one_le_ep_of_curve Q hC ζ) hT1 hcp hv hν
    (X.Ol la) (Op X la G.N) (X.Kl la) (Kp X la G.N) ↥(T0.WL X (addL wF wL T) la) ↥(Vw X la G.N (addL wF wL T))
    (WK X la G.w wF (a0 D j T)) (jW X la G.N (addL wF wL T)) (jW_isBaseChange X la G.N _ hM.span_eq_top)
    (unif X la) (unif_irreducible X la) (unifO_irreducible X la G.N)
    (T0.MW X (addL wF wL T) la) (T0.ThW X S (addL wF wL T) wL wF T la) (MggW X la (addL wF wL T) CRm T c)
    (N1 G la) (Zl G la) (Zm G la) (Np G la e) e G.rq
    (WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j (addL wF wL T) ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j (addL wF wL T))))).toNat
    (fun i => toW X la (addL wF wL T) (G.th i)) (Q.AA T) (Q.AAp T (Q.mm S T e)) (firstLength_le_prime_bound G la T) (rhoN G la e)
    hLat.1 hLat.2 (sup_le hN1 hZ1) (fun i => toW_mem_MW X la _ (G.th i))
    hthΘ
    (Submodule.comap_mono (Submodule.span_mono (Set.image_mono (T0.emb_mono X _ inf_le_left))))
    (fun x hx => jW_MggW_mem G la S CRm c hΘM hw hth' hth0 hal hCM x hx)
    ((quot_len_le X la (addL wF wL T) CRm T c G.th).trans (le_of_eq (ENat.natCast_toNat hqne).symm))
    (le_sup_of_le_left le_sup_left) (generators_le_poleSpan G la e) (Zl_le_Zm G la (hZ1.trans hTM)) (Zm_le_Np G la e)
    (rhoN_mem G Q S e hC hTie hw hth'M hDT hal) (ker_rhoN G la e (in64 G la hB) (hN1.trans hTM) hDT hal)
    (map_reduction_generators_eq G la e) (reduced_generators_le Q S hC hTie hw hth'M) (AA_le_AAp Q _)
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hZlen) (Or.inl ⟨he, fun ζ => ep_nu_int Q hTie ζ⟩) hLP' hLB U
  have hZn : ((Module.length (Op X la G.N) (↥(Zm G la) ⧸ (Zl G la).comap (Zm G la).subtype)).toNat : ℝ) ≤
      (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j (addL wF wL T)) G.zc la : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hZlen
  linarith

end

theorem localBound {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X ka wL wF)
    (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm c : ℝ) (e : ℕ) (νs : ℝ)
    (hka : ka = addL wF wL T)
    (hM : Submodule.IsLattice B.KO (B.Mlat j ka)) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka)
    (hspK : Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤)
    (hT1 : 1 ≤ T) (hDT : WeightFamilies.dimY D j ≤ T)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hwM : ∀ k, G.w k ∈ B.Mlat j wL)
    (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF) (hth'M : ∀ i, G.th' i ∈ B.Mlat j wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hth0M : ∀ k, G.th0 k ∈ B.Mlat j (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hzc : ∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β)
    (hdet : ∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)
    (hthK : ∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka)
    (hsp : Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤)
    (hB : InBasis G la) (hC : Q.InCurve) (hTie : Q.InTie S)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) ''
        (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (hv : ∀ ζ, 0 ≤ vEt Q ζ) (hν : ∀ ζ, Q.nu S ζ ≤ νs + max 0 c * vEt Q ζ) (he : (T : ℝ) * νs ≤ (e : ℝ))
    (hLB : Module.length (Op X la G.N) (↥(Q.AA T) ⧸ (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * Q.Ila.toNat : ℕ) : ℕ∞))
    (hLP : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞))
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (finrank (X.Kl la) V' : ℝ) + rLa Q CRm T c := by
  subst hka
  have := (finite_pts_of_curve Q hC).1
  letI := Fintype.ofFinite (PtsG G la)
  refine qlen_of_idx X S _ wL wF T la (inLat_of X S _ wL wF T la hM hΘM hspK) hΘM e (rLa Q CRm T c) (fun U => ?_) V' hV'
  have h := localIdx G la Q S CRm c e νs (max 0 c) (vEt Q) hM hΘM hspK hT1 hDT hw hwM hth' hth'M hth0 hth0M hal hzc hdet
    hthK hsp hB hC hTie hCM (le_max_left _ _) hv hν he hLB hLP U
  rw [levels_eq Q T c] at h
  unfold rLa
  linarith

end Formalism.MainNotions.Gaps.EtaleWeightGaps
