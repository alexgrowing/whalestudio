import Development.EtaleCohomology.KummerTheory.PlaceExPf

noncomputable section

namespace LateralTheory.KummerTheory.PlaceZornPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem good_range : PlaceGood k K (LocalSubring.range (algebraMap k K)) := by
  refine ⟨fun c => ⟨c, rfl⟩, ?_⟩
  rintro a ⟨c, rfl⟩
  exact ⟨c, Or.inl rfl⟩

theorem ub (s : Set (LocalSubring K)) (hs : s ⊆ {A | PlaceGood k K A}) (H : IsChain (· ≤ ·) s)
    (y : LocalSubring K) (hys : y ∈ s) :
    ∃ U ∈ {A | PlaceGood k K A}, ∀ z ∈ s, z ≤ U := by
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
  · refine ⟨fun c => ?_, ?_⟩
    · exact le_iSup (fun i : s ↦ i.1.toSubring) ⟨y, hys⟩ ((hs hys).1 c)
    · intro a ha
      obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
      obtain ⟨c, hc⟩ := (hs A.2).2 a haA
      refine ⟨c, hc.imp_right fun hn hinv => hn ?_⟩
      obtain ⟨B, hbB : (a - algebraMap k K c)⁻¹ ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hinv
      obtain ⟨C, hCA, hCB⟩ := H.directed A B
      have hd : a - algebraMap k K c ∈ A.1.toSubring := sub_mem haA ((hs A.2).1 c)
      have hne : a - algebraMap k K c ≠ 0 := by
        intro h0; rw [h0, inv_zero] at hn; exact hn (zero_mem _)
      have hu : IsUnit (⟨a - algebraMap k K c, hCA.1 hd⟩ : C.1.toSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨_, hCB.1 hbB⟩, Subtype.ext (by simp [mul_inv_cancel₀ hne])⟩
      have hu' : IsUnit (⟨a - algebraMap k K c, hd⟩ : A.1.toSubring) := by
        have := hCA.2
        apply IsUnit.of_map (Subring.inclusion hCA.1)
        exact hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu'
      have : (a - algebraMap k K c)⁻¹ = (w : K) :=
        inv_eq_of_mul_eq_one_right (by simpa using congrArg Subtype.val hw)
      rw [this]; exact w.2
  · intro A hA
    refine ⟨le_iSup (fun i : s ↦ i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

end LateralTheory.KummerTheory.PlaceZornPf

theorem LateralTheory.KummerTheory.PlaceZorn_of : LateralTheory.KummerTheory.PlaceZorn := by
  intro k K _ _ _ _
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ {A : LocalSubring K | LateralTheory.KummerTheory.PlaceGood k K A}
    (fun s hs H y hy => LateralTheory.KummerTheory.PlaceZornPf.ub s hs H y hy) _ LateralTheory.KummerTheory.PlaceZornPf.good_range
  exact ⟨m, hm.1, fun B hB hgB => hm.2 hgB hB⟩

theorem LateralTheory.KummerTheory.PlaceEx_of_step (h : LateralTheory.KummerTheory.PlaceStep) : LateralTheory.KummerTheory.PlaceEx :=
  LateralTheory.KummerTheory.PlaceEx_of LateralTheory.KummerTheory.PlaceZorn_of h
